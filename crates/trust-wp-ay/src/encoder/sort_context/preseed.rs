// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort pre-seeding and domain hint propagation.
//!
//! Batch pre-scan operations that prepare the sort context before encoding
//! begins. These methods run after function signatures are declared but
//! before variable pre-declaration:
//!
//! - `preseed_constructor_var_sort`: Pre-seed variable sort from datatype constructors
//! - `collect_declared_fn_domain_sorts_batch`: Collect domain sorts from
//!   declared logic functions for the bootstrap sort plan
//! - `preseed_int_model_type_sort`: Pre-declare Int sort for Int-model Datatype annotations

use std::collections::{hash_map::Entry, HashMap, HashSet};

use ay_dpll::api::Sort;
use trust_wp_core::{
    formula::{ExprSort, PureExpr, PureExprDepthLimitedTraversalExt as _},
    logic::LogicFnDef,
};

use super::{
    extract_base_var_name, extract_constructor_name, is_seq_family_sort, resolve_view_var_name,
    sort_mapping::{retarget_seq_carrier, SeqCarrier},
};
use crate::encoder::{state::DeclarationState, AYEncoder};

impl AYEncoder {
    /// Pre-seed variable sort for datatype constructors. (#1572)
    pub(in crate::encoder) fn preseed_constructor_var_sort(&mut self, l: &PureExpr, r: &PureExpr) {
        self.preseed_constructor_var_sort_directed(l, r);
        self.preseed_constructor_var_sort_directed(r, l);
    }

    fn preseed_constructor_var_sort_directed(&mut self, var_side: &PureExpr, ctor_side: &PureExpr) {
        let Some(var_name) = extract_base_var_name(var_side) else {
            return;
        };
        let ctor_name = extract_constructor_name(ctor_side).or_else(|| match ctor_side {
            PureExpr::Var(name, _) if self.nullary_constructor_datatype(name).is_some() => {
                Some(name.as_str())
            }
            _ => None,
        });
        let Some(ctor_name) = ctor_name else {
            return;
        };
        if let Some(arity) =
            trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_arity(ctor_name)
        {
            let tuple_sort = Sort::Uninterpreted(format!("Tuple{arity}"));
            if !self.has_var_sort(var_name) || matches!(self.var_sort(var_name), Some(Sort::Int)) {
                self.insert_var_sort(var_name.to_string(), tuple_sort);
            }
            return;
        }
        let Some(dt) = self
            .nullary_constructor_datatype(ctor_name)
            .or_else(|| self.constructor_datatype(ctor_name))
        else {
            return;
        };
        let dt_sort = Sort::Datatype(dt);
        if !self.has_var_sort(var_name) || matches!(self.var_sort(var_name), Some(Sort::Int)) {
            self.insert_var_sort(var_name.to_string(), dt_sort);
        }
    }

    /// Pre-declare a variable with `Sort::Int` when it has a Datatype annotation
    /// that models as an integer (Duration, Instant, Ghost, NonZero*, etc.).
    ///
    /// This is a defense-in-depth measure for arithmetic operators. When the MIR
    /// annotation says a variable's type is an Int-model Datatype (e.g.,
    /// `ExprSort::Datatype("std::time::Duration")`), this pre-declares it with
    /// `Sort::Int` before encoding so that `encode_var` → `get_or_declare_var`
    /// finds the correct sort on first encounter. (#1965)
    ///
    /// If the variable was already declared with a wrong `Uninterpreted` sort
    /// by a different code path, this redeclares it with Int via the same
    /// `__upgraded` mechanism used by `get_or_declare_var`.
    pub(in crate::encoder) fn preseed_int_model_type_sort(
        &mut self,
        expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) {
        let (name, ann) = match expr {
            PureExpr::Var(name, ann) => (name.as_str(), ann.as_ref()),
            PureExpr::Deref(inner) | PureExpr::Final(inner) | PureExpr::Old(inner) => {
                if let PureExpr::Var(name, ann) = inner.as_ref() {
                    (name.as_str(), ann.as_ref())
                } else {
                    return;
                }
            }
            _ => return,
        };
        let Some(ann) = ann else { return };
        // Only fire for Datatype (or Ref(Datatype)) annotations that map to Int.
        // ExprSort::Int already produces Int, and Var(_, None) defaults to Int.
        // This guard prevents firing on every Int variable (wasteful no-ops).
        if !matches!(ann, ExprSort::Datatype(_) | ExprSort::Ref(_)) {
            return;
        }
        // Check if the annotation is a Datatype that should be Int.
        let sort = super::sort_inference::expr_sort_to_ay_sort(ann);
        if sort != Sort::Int {
            return;
        }
        // The annotation is a Datatype that maps to Int. Ensure the variable
        // is declared/redeclared with Int sort.
        let var_name: std::borrow::Cow<'_, str> = match prefix {
            Some(kind) => std::borrow::Cow::Owned(kind.format_name(name)),
            None => std::borrow::Cow::Borrowed(name),
        };
        if let Some(existing) = self.var_sort(var_name.as_ref()).cloned() {
            if existing != Sort::Int {
                // Already declared with a wrong sort. Redeclare with Int.
                // Use the same __upgraded mechanism as get_or_declare_var.
                tracing::debug!(
                    var = %var_name,
                    from = ?existing,
                    "preseed_int_model_type_sort: redeclaring as Int"
                );
                let new_term = self.declare_derived_source_var(&var_name, "upgrade", Sort::Int);
                self.insert_var(var_name.to_string(), new_term);
                self.insert_var_sort(var_name.to_string(), Sort::Int);
            }
            // Already Int — no-op.
        } else {
            // Not yet declared — pre-declare with Int so the first declaration
            // wins with the correct sort.
            let _ = self.get_or_declare_var(&var_name, Sort::Int);
        }
    }

    /// Seed the current logic function's parameters from already-declared
    /// function domains before signature resolution. (#2002)
    ///
    /// This reuses the same declared-domain collection path as verification
    /// bootstrap, but filters the writes to the current parameter names so the
    /// shared `var_sorts` table only learns the sorts that matter for the
    /// declaration being computed right now.
    pub(in crate::encoder) fn preseed_logic_param_domain_sorts(&mut self, logic_fn: &LogicFnDef) {
        let param_names: HashSet<&str> = logic_fn.params().iter().map(String::as_str).collect();
        if param_names.is_empty() {
            return;
        }

        let exprs: Vec<&PureExpr> = logic_fn
            .requires()
            .iter()
            .chain(logic_fn.ensures().iter())
            .chain(std::iter::once(logic_fn.body()))
            .collect();
        let planned = collect_declared_fn_domain_sorts_batch(self.decls(), &exprs);

        let carrier = self.seq_carrier();
        for (name, sort) in planned {
            // Domain sorts come from already-declared function signatures and
            // from `LogicFnDef::param_sorts` via the stateless converter, so a
            // Seq domain can arrive spelled on either carrier. Retarget before
            // it becomes this encoder's var sort. (See `SeqCarrier`.)
            let sort = retarget_seq_carrier(sort, carrier);
            if sort == Sort::Int || !param_names.contains(name.as_str()) {
                continue;
            }

            let should_insert = self.var_sort(&name).is_none_or(|existing| {
                domain_sort_specificity(&sort) > domain_sort_specificity(existing)
            });
            if should_insert {
                self.insert_var_sort(name, sort);
            }
        }
    }
}

/// Collect planned declaration sorts from declared logic-function domains.
///
/// This is the bootstrap-side counterpart to `propagate_domain_sort_hints` in
/// `call_encoding.rs`: it walks the expressions, looks up already-declared
/// function domains, and returns the names that should be predeclared before
/// encoding begins. Unlike the old mutation helper, it keeps collection pure
/// so bootstrap can route the result through `SortPlan`. (#2020)
pub(crate) fn collect_declared_fn_domain_sorts_batch(
    decls: &DeclarationState,
    exprs: &[&PureExpr],
) -> HashMap<String, Sort> {
    let mut planned = HashMap::new();
    for expr in exprs {
        collect_declared_fn_domain_sorts_expr(decls, expr, &mut planned);
    }
    planned
}

fn collect_declared_fn_domain_sorts_expr(
    decls: &DeclarationState,
    expr: &PureExpr,
    planned: &mut HashMap<String, Sort>,
) {
    expr.for_each_recursive_with_depth_limit(super::super::MAX_ENCODING_DEPTH, |node| match node {
        PureExpr::LogicFnCall { name, args } => {
            let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
            let Some(fd) = decls.get_logic_func(&smt_name) else {
                return;
            };
            collect_domain_sort_targets_for_args(args.iter(), fd.domain(), planned);
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let smt_name = trust_wp_core::logic::logic_fn_smt_name(method);
            let Some(fd) = decls.get_logic_func(&smt_name) else {
                return;
            };
            collect_method_domain_sort_targets(receiver, args, fd.domain(), planned);
        }
        _ => {}
    });
}

fn collect_domain_sort_targets_for_args<'a>(
    args: impl Iterator<Item = &'a PureExpr>,
    domain: &[Sort],
    planned: &mut HashMap<String, Sort>,
) {
    for (arg, sort) in args.zip(domain.iter()) {
        collect_domain_sort_targets(arg, sort, planned);
    }
}

fn collect_method_domain_sort_targets(
    receiver: &PureExpr,
    args: &[PureExpr],
    domain: &[Sort],
    planned: &mut HashMap<String, Sort>,
) {
    let Some(receiver_sort) = domain.first() else {
        return;
    };
    collect_domain_sort_targets(receiver, receiver_sort, planned);
    collect_domain_sort_targets_for_args(args.iter(), &domain[1..], planned);
}

fn collect_domain_sort_targets(arg: &PureExpr, sort: &Sort, out: &mut HashMap<String, Sort>) {
    // Skip Int — it's the default fallback and provides no information.
    if *sort == Sort::Int {
        return;
    }

    if is_seq_family_sort(sort) || matches!(sort, Sort::Uninterpreted(name) if name == "FMap") {
        if let Some(name) = resolve_view_var_name(arg, None) {
            record_domain_sort(out, name, sort.clone());
        }
        if let Some(name) = super::resolve_nameable_expr(arg, None) {
            record_domain_sort(out, name, sort.clone());
        }
        return;
    }

    // For all other non-Int sorts (Datatype, Bool, generic Uninterpreted),
    // use extract_base_var_name which handles Var, Deref, Final, Old, View
    // wrappers. This generalises the previous Datatype-only path to cover
    // Bool and custom Uninterpreted domain sorts that were previously
    // missed, causing passthrough parameters to fall through to Sort::Int.
    // (#2002)
    if let Some(base_name) = extract_base_var_name(arg) {
        record_domain_sort(out, base_name.to_string(), sort.clone());
    }
}

fn record_domain_sort(out: &mut HashMap<String, Sort>, name: String, sort: Sort) {
    match out.entry(name) {
        Entry::Occupied(mut existing) => {
            if domain_sort_specificity(&sort) > domain_sort_specificity(existing.get()) {
                existing.insert(sort);
            }
        }
        Entry::Vacant(vacant) => {
            vacant.insert(sort);
        }
    }
}

fn domain_sort_specificity(sort: &Sort) -> u8 {
    // Both Seq carriers rank identically — see `sort_specificity` in `plan.rs`.
    // Domain sorts read back from already-declared function signatures carry
    // whichever carrier the encoder chose, so without this the same evidence
    // would rank 2 in one lane and 4 in another.
    if SeqCarrier::classify(sort).is_some() {
        return 2;
    }
    match sort {
        Sort::Int => 0,
        Sort::Bool => 1,
        Sort::Seq(_) => 2,
        Sort::Uninterpreted(name) if name == "FMap" => 3,
        Sort::Datatype(_) => 4,
        Sort::Uninterpreted(_) => 4,
        _ => 2,
    }
}

/// Collect domain sort evidence from `LogicFnDef::param_sorts` for call-site
/// arguments that appear in `exprs`.
///
/// This complements `collect_declared_fn_domain_sorts_batch` which only covers
/// logic functions already declared on the encoder. At bootstrap time, the logic
/// functions from the verification request have not been registered yet, so their
/// `param_sorts` metadata is invisible to the declared-function path. This
/// function bridges that gap by matching `LogicFnCall` nodes in the expression
/// tree against the provided `LogicFnDef` slice and propagating each non-default
/// param sort to the corresponding call-site argument name.
pub(crate) fn collect_logic_fn_def_domain_sorts(
    exprs: &[&PureExpr],
    logic_fns: &[LogicFnDef],
) -> HashMap<String, Sort> {
    if logic_fns.is_empty() {
        return HashMap::new();
    }

    let mut fn_by_name_and_arity: HashMap<(&str, usize), Vec<&LogicFnDef>> = HashMap::new();
    for logic_fn in logic_fns {
        let arity = logic_fn.params().len();
        fn_by_name_and_arity
            .entry((logic_fn.name(), arity))
            .or_default()
            .push(logic_fn);
        if logic_fn.full_path() != logic_fn.name() {
            fn_by_name_and_arity
                .entry((logic_fn.full_path(), arity))
                .or_default()
                .push(logic_fn);
        }
    }
    let mut planned = HashMap::new();
    for expr in exprs {
        collect_logic_fn_def_domain_sorts_expr(expr, &fn_by_name_and_arity, &mut planned);
    }
    planned
}

/// Collect parameter-name sort evidence only for logic functions whose own
/// contracts are part of the current goal.
///
/// This covers logic postcondition checks where a parameter appears as a bare
/// variable or method receiver inside that function's own `ensures`, while
/// avoiding the old global preseed that mapped common names like `self` and
/// `result` from unrelated visible functions into every obligation.
pub(crate) fn collect_active_logic_fn_param_name_sorts(
    goal_exprs: &[&PureExpr],
    logic_fns: &[LogicFnDef],
) -> HashMap<String, Sort> {
    let mut planned = HashMap::new();
    for logic_fn in logic_fns {
        if !logic_fn_is_active_in_goal(logic_fn, goal_exprs) {
            continue;
        }
        collect_logic_fn_param_name_sorts(logic_fn, &mut planned);
    }
    planned
}

fn logic_fn_is_active_in_goal(logic_fn: &LogicFnDef, goal_exprs: &[&PureExpr]) -> bool {
    goal_exprs.iter().any(|goal| {
        logic_fn.requires().iter().any(|req| req == *goal)
            || logic_fn.ensures().iter().any(|ens| ens == *goal)
    })
}

fn collect_logic_fn_param_name_sorts(logic_fn: &LogicFnDef, planned: &mut HashMap<String, Sort>) {
    for (param_name, param_sort_opt) in logic_fn.params().iter().zip(logic_fn.param_sorts().iter())
    {
        let Some(expr_sort) = param_sort_opt else {
            continue;
        };
        let sort = super::expr_sort_to_ay_sort(expr_sort);
        if sort == Sort::Int {
            continue;
        }
        record_domain_sort(planned, param_name.clone(), sort);
    }
}

fn collect_logic_fn_def_domain_sorts_expr(
    expr: &PureExpr,
    fn_by_name_and_arity: &HashMap<(&str, usize), Vec<&LogicFnDef>>,
    planned: &mut HashMap<String, Sort>,
) {
    expr.for_each_recursive_with_depth_limit(super::super::MAX_ENCODING_DEPTH, |node| match node {
        PureExpr::LogicFnCall { name, args } => {
            let Some(candidates) = fn_by_name_and_arity.get(&(name.as_str(), args.len())) else {
                return;
            };
            let Some(def) = select_logic_fn_domain_def(name, args, candidates, planned) else {
                return;
            };
            collect_logic_fn_def_domain_sort_targets(args.iter(), def, planned);
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let arity = args.len() + 1;
            let Some(candidates) = fn_by_name_and_arity.get(&(method.as_str(), arity)) else {
                return;
            };
            let Some(def) = select_method_domain_def(method, receiver, args, candidates, planned)
            else {
                return;
            };
            let Some(receiver_sort) = def.param_sorts().first().and_then(Option::as_ref) else {
                return;
            };
            let sort = super::expr_sort_to_ay_sort(receiver_sort);
            collect_domain_sort_targets(receiver, &sort, planned);
            collect_logic_fn_def_domain_sort_targets_for_param_sorts(
                args.iter(),
                &def.param_sorts()[1..],
                planned,
            );
        }
        _ => {}
    });
}

fn select_logic_fn_domain_def<'a>(
    name: &str,
    args: &[PureExpr],
    candidates: &[&'a LogicFnDef],
    planned: &HashMap<String, Sort>,
) -> Option<&'a LogicFnDef> {
    if method_domain_requires_receiver_evidence(name)
        && args
            .first()
            .is_none_or(|arg| expr_sort_evidence(arg, planned).is_none())
    {
        return None;
    }
    select_domain_def(candidates, |def| {
        call_args_match_domain(args.iter(), def.param_sorts(), planned)
    })
}

fn select_method_domain_def<'a>(
    method: &str,
    receiver: &PureExpr,
    args: &[PureExpr],
    candidates: &[&'a LogicFnDef],
    planned: &HashMap<String, Sort>,
) -> Option<&'a LogicFnDef> {
    if method_domain_requires_receiver_evidence(method)
        && expr_sort_evidence(receiver, planned).is_none()
    {
        return None;
    }
    select_domain_def(candidates, |def| {
        let param_sorts = def.param_sorts();
        let Some(receiver_sort) = param_sorts.first() else {
            return false;
        };
        expr_matches_domain_sort(receiver, receiver_sort.as_ref(), planned)
            && call_args_match_domain(args.iter(), &param_sorts[1..], planned)
    })
}

fn method_domain_requires_receiver_evidence(method: &str) -> bool {
    method == "index_logic"
}

fn select_domain_def<'a>(
    candidates: &[&'a LogicFnDef],
    matches: impl Fn(&LogicFnDef) -> bool,
) -> Option<&'a LogicFnDef> {
    if candidates.len() == 1 {
        return matches(candidates[0]).then_some(candidates[0]);
    }
    let mut compatible = candidates.iter().copied().filter(|def| matches(def));
    let first = compatible.next()?;
    if compatible.next().is_none() {
        Some(first)
    } else {
        None
    }
}

fn call_args_match_domain<'a>(
    args: impl Iterator<Item = &'a PureExpr>,
    param_sorts: &[Option<ExprSort>],
    planned: &HashMap<String, Sort>,
) -> bool {
    args.zip(param_sorts.iter())
        .all(|(arg, sort)| expr_matches_domain_sort(arg, sort.as_ref(), planned))
}

fn expr_matches_domain_sort(
    expr: &PureExpr,
    expected: Option<&ExprSort>,
    planned: &HashMap<String, Sort>,
) -> bool {
    let Some(evidence) = expr_sort_evidence(expr, planned) else {
        return true;
    };
    let expected = expected
        .map(super::expr_sort_to_ay_sort)
        .unwrap_or(Sort::Int);
    domain_sorts_compatible(&evidence, &expected)
}

fn expr_sort_evidence(expr: &PureExpr, planned: &HashMap<String, Sort>) -> Option<Sort> {
    if let Some(annotation) = super::effective_expr_annotation(expr) {
        let sort = super::expr_sort_to_ay_sort(annotation);
        if sort != Sort::Int {
            return Some(sort);
        }
    }

    resolve_view_var_name(expr, None)
        .or_else(|| super::resolve_nameable_expr(expr, None))
        .or_else(|| extract_base_var_name(expr).map(ToOwned::to_owned))
        .and_then(|name| planned.get(&name).cloned())
        .filter(|sort| *sort != Sort::Int)
}

fn domain_sorts_compatible(evidence: &Sort, expected: &Sort) -> bool {
    evidence == expected || (is_seq_family_sort(evidence) && is_seq_family_sort(expected))
}

fn collect_logic_fn_def_domain_sort_targets<'a>(
    args: impl Iterator<Item = &'a PureExpr>,
    def: &LogicFnDef,
    planned: &mut HashMap<String, Sort>,
) {
    collect_logic_fn_def_domain_sort_targets_for_param_sorts(args, def.param_sorts(), planned);
}

fn collect_logic_fn_def_domain_sort_targets_for_param_sorts<'a>(
    args: impl Iterator<Item = &'a PureExpr>,
    param_sorts: &[Option<ExprSort>],
    planned: &mut HashMap<String, Sort>,
) {
    for (arg, param_sort_opt) in args.zip(param_sorts.iter()) {
        let Some(expr_sort) = param_sort_opt else {
            continue;
        };
        let sort = super::expr_sort_to_ay_sort(expr_sort);
        collect_domain_sort_targets(arg, &sort, planned);
    }
}
