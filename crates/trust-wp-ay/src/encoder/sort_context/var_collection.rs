// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Two-phase variable collection for deferred sort declaration.
//!
//! Walks `PureExpr` trees and collects all variable usage evidence into
//! per-variable records *before* encoding begins. This eliminates the
//! ordering constraint from `get_or_declare_var`'s first-declaration-wins
//! semantics by determining each variable's sort from its complete usage
//! context.
//!
//! Part of #1965 — deferred-declaration alternative design.

use std::collections::HashMap;

use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_index, tuple_logic_fn_arity},
    BinOp, ExprSort, PureExpr, UnOp,
};

use super::{resolve_view_var_name, sort_inference::expr_sort_to_ay_sort};
use crate::encoder::seq::is_seq_only_method;

/// Collected evidence about a variable's sort from expression context.
#[derive(Debug, Clone, Default)]
pub(crate) struct VarUsage {
    /// ExprSort annotation from MIR (if present on any Var node).
    pub annotation: Option<ExprSort>,
    /// Tuple constructor evidence from `var == __trust_wp_tupleN(...)`. (#994)
    pub tuple_arity: Option<usize>,
    /// Tuple-projection evidence came from a direct (non-view) projection
    /// such as `tuple_get_N(Var("y"))` rather than `tuple_get_N(View(Var("y")))`.
    ///
    /// Direct projections on a variable that also carries a registered
    /// `Datatype` annotation are the ADT field accessor pattern (e.g. `y.0`
    /// on a struct `Zero<T>`), not a logical tuple model. The sort plan
    /// uses this signal together with the registered-datatype check to
    /// prefer the annotation in that case and avoid the `Tuple1` vs ADT
    /// sort conflict in closures/10_tyinv.
    pub tuple_arity_from_direct_projection: bool,
    /// ADT constructor family evidence from `var == Ctor(...)` equalities. (#2700)
    ///
    /// When a variable appears in equality with a known constructor
    /// (Some/None/Ok/Err), this records the constructor family name
    /// ("Option" or "Result"). Used during sort determination to avoid
    /// sort_fallback_to_int for variables constrained by constructor equalities
    /// in proof_assert preconditions.
    pub constructor_family: Option<String>,
    /// Method calls on this variable (e.g., "len" -> Seq evidence).
    pub method_calls: Vec<String>,
    /// Appears as receiver of View (expr@) -> likely Seq/collection.
    pub has_view: bool,
    /// Appears in Deref/Final context -> mutable borrow encoding.
    pub has_borrow_context: bool,
    /// Appears in boolean position (If condition, And/Or operand).
    pub in_bool_context: bool,
    /// Appears in equality/disequality with an integer literal outside
    /// {0, 1} (e.g. `rc3@ == 2`). Such a variable cannot be Bool under a
    /// faithful encoding: ay's `eq()` bridges Bool-vs-Int through the 0/1
    /// lane, so a Bool-sorted variable compared to an out-of-range literal
    /// forces the equality to be replaced by a polarity-neutral placeholder
    /// (`__trust_wp_unencodable_eq_*`), fabricating the premise away and
    /// producing false counterexamples (arc_and_rc flake). This evidence
    /// vetoes the heuristic `in_bool_context -> Bool` inference and strips
    /// heuristic Bool sort hints during sort planning, making the planned
    /// sort independent of hash-iteration order.
    pub int_literal_eq: bool,
    /// ExprSort from Forall/Exists bound variable declarations.
    pub quantifier_sort: Option<ExprSort>,
}

impl VarUsage {
    /// Merge another usage record into this one (union of evidence).
    pub(crate) fn merge(&mut self, other: VarUsage) {
        if should_replace_annotation(self.annotation.as_ref(), other.annotation.as_ref()) {
            self.annotation = other.annotation;
        }
        self.tuple_arity = match (self.tuple_arity, other.tuple_arity) {
            (Some(current), Some(incoming)) => Some(current.max(incoming)),
            (Some(current), None) => Some(current),
            (None, incoming) => incoming,
        };
        self.tuple_arity_from_direct_projection |= other.tuple_arity_from_direct_projection;
        if self.constructor_family.is_none() {
            self.constructor_family = other.constructor_family;
        }
        self.method_calls.extend(other.method_calls);
        self.has_view |= other.has_view;
        self.has_borrow_context |= other.has_borrow_context;
        self.in_bool_context |= other.in_bool_context;
        self.int_literal_eq |= other.int_literal_eq;
        if should_replace_annotation(
            self.quantifier_sort.as_ref(),
            other.quantifier_sort.as_ref(),
        ) {
            self.quantifier_sort = other.quantifier_sort;
        }
    }
}

fn should_replace_annotation(current: Option<&ExprSort>, incoming: Option<&ExprSort>) -> bool {
    match (current, incoming) {
        (None, Some(_)) => true,
        (Some(existing), Some(next)) => {
            expr_sort_to_ay_sort(existing) == ay_dpll::api::Sort::Int
                && expr_sort_to_ay_sort(next) != ay_dpll::api::Sort::Int
        }
        _ => false,
    }
}

/// Walk a `PureExpr` tree and collect all variable usage evidence.
///
/// This is a pure function: no solver interaction, no mutation beyond
/// the output map. Independently testable.
pub(crate) fn collect_variable_usage(exprs: &[PureExpr]) -> HashMap<String, VarUsage> {
    let mut usage: HashMap<String, VarUsage> = HashMap::new();
    for expr in exprs {
        collect_from_expr(expr, &mut usage, false);
    }
    usage
}

/// Like [`collect_variable_usage`], but treats each top-level expression as
/// a formula (boolean-position). Use this for requires/ensures expressions,
/// which ARE boolean-valued — a bare `Var("b")` in ensures means `b` is Bool.
///
/// This replaces the semantics of the removed `register_formula_sort_hints`,
/// which treated its inputs as formula-position expressions.
pub(crate) fn collect_variable_usage_as_formula(exprs: &[PureExpr]) -> HashMap<String, VarUsage> {
    let mut usage: HashMap<String, VarUsage> = HashMap::new();
    for expr in exprs {
        collect_from_expr(expr, &mut usage, true);
    }
    usage
}

/// Recursive AST walker. `in_bool_ctx` tracks whether we're in a position
/// that expects a boolean value (If condition, And/Or operand, etc.).
fn collect_from_expr(expr: &PureExpr, usage: &mut HashMap<String, VarUsage>, in_bool_ctx: bool) {
    match expr {
        PureExpr::Var(name, ann) => {
            collect_var_usage(name, ann.as_ref(), in_bool_ctx, usage);
        }
        PureExpr::View(inner) => {
            if let Some(name) = extract_base_var(inner) {
                usage.entry(name).or_default().has_view = true;
            }
            collect_from_expr(inner, usage, false);
        }
        PureExpr::Deref(inner) | PureExpr::Final(inner) => {
            if let Some(name) = extract_base_var(inner) {
                usage.entry(name).or_default().has_borrow_context = true;
            }
            collect_from_expr(inner, usage, false);
        }
        PureExpr::Old(inner) => collect_from_expr(inner, usage, in_bool_ctx),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => collect_method_call(receiver, method, args, usage),
        PureExpr::LogicFnCall { name, args } => {
            if let Some(field_idx) = tuple_field_logic_fn_index(name) {
                if args.len() == 1 {
                    collect_tuple_projection_evidence(&args[0], field_idx, usage);
                }
            }
            collect_children(args, usage);
        }
        PureExpr::Forall {
            var,
            var_sort,
            body,
            triggers,
        }
        | PureExpr::Exists {
            var,
            var_sort,
            body,
            triggers,
        } => collect_quantifier(var, var_sort.as_ref(), body, triggers, usage),
        PureExpr::BinOp(l, op, r) => {
            if matches!(op, BinOp::Eq | BinOp::Ne) {
                collect_tuple_constructor_evidence(l, r, usage);
                collect_tuple_constructor_evidence(r, l, usage);
                // Collect ADT constructor evidence: `var == Ctor(...)` where
                // Ctor is Some/None/Ok/Err. This prevents sort_fallback_to_int
                // for variables constrained by constructor equalities in
                // proof_assert preconditions. (#2700)
                collect_constructor_equality_evidence(l, r, usage);
                collect_constructor_equality_evidence(r, l, usage);
                // Collect int-literal-equality evidence: `var == 2` (or any
                // literal outside {0,1}) proves the variable cannot be Bool.
                // Consumed by `determine_sort` (vetoes the in_bool_context
                // Bool inference) and by `SortPlanBuilder::build` (strips
                // heuristic Bool sort hints). (arc_and_rc sort-plan flake)
                collect_int_literal_equality_evidence(l, r, usage);
                collect_int_literal_equality_evidence(r, l, usage);
            }
            let bool_ctx = matches!(op, BinOp::And | BinOp::Or | BinOp::Implies);
            collect_from_expr(l, usage, bool_ctx);
            collect_from_expr(r, usage, bool_ctx);
        }
        PureExpr::UnOp(UnOp::Not, inner) => collect_from_expr(inner, usage, true),
        PureExpr::UnOp(_, inner) => collect_from_expr(inner, usage, false),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            collect_from_expr(cond, usage, true);
            collect_from_expr(then_expr, usage, false);
            collect_from_expr(else_expr, usage, false);
        }
        PureExpr::Match { scrutinee, arms } => collect_match(scrutinee, arms, usage),
        PureExpr::Let { value, body, .. } => collect_pair(value, body, usage, false),
        PureExpr::Closure { params, body } => {
            for (name, sort) in params {
                if let Some(s) = sort {
                    usage.entry(name.clone()).or_default().annotation = Some(s.clone());
                }
            }
            collect_from_expr(body, usage, false);
        }
        PureExpr::LetAssume { assumption, body } => collect_pair(assumption, body, usage, true),
        PureExpr::LetObligation { obligation, body } => {
            collect_pair(obligation, body, usage, true);
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => {}
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => {}
    }
}

/// Collect usage from a method call: record the method on the receiver's base var.
fn collect_method_call(
    receiver: &PureExpr,
    method: &str,
    args: &[PureExpr],
    usage: &mut HashMap<String, VarUsage>,
) {
    if let Some(name) = extract_base_var(receiver) {
        usage
            .entry(name)
            .or_default()
            .method_calls
            .push(method.to_string());
    }
    collect_from_expr(receiver, usage, false);
    collect_children(args, usage);
}

/// Collect usage from a quantifier binding.
fn collect_quantifier(
    var: &str,
    var_sort: Option<&ExprSort>,
    body: &PureExpr,
    triggers: &[Vec<PureExpr>],
    usage: &mut HashMap<String, VarUsage>,
) {
    if let Some(sort) = var_sort {
        usage.entry(var.to_string()).or_default().quantifier_sort = Some(sort.clone());
    }
    collect_from_expr(body, usage, false);
    for trigger in triggers {
        collect_children(trigger, usage);
    }
}

/// Collect usage from a match expression.
fn collect_match(
    scrutinee: &PureExpr,
    arms: &[trust_wp_core::formula::MatchArm],
    usage: &mut HashMap<String, VarUsage>,
) {
    collect_from_expr(scrutinee, usage, false);
    for arm in arms {
        let mut arm_usage = HashMap::new();
        collect_from_expr(&arm.body, &mut arm_usage, false);
        for bound_name in arm.pattern.bound_names() {
            arm_usage.remove(bound_name);
        }
        for (name, arm_var_usage) in arm_usage {
            usage.entry(name).or_default().merge(arm_var_usage);
        }
    }
}

/// Collect usage from two child expressions (Let, LetAssume, LetObligation).
fn collect_pair(
    first: &PureExpr,
    second: &PureExpr,
    usage: &mut HashMap<String, VarUsage>,
    first_is_bool: bool,
) {
    collect_from_expr(first, usage, first_is_bool);
    collect_from_expr(second, usage, false);
}

/// Collect usage from a slice of child expressions (args, triggers).
fn collect_children(exprs: &[PureExpr], usage: &mut HashMap<String, VarUsage>) {
    for expr in exprs {
        collect_from_expr(expr, usage, false);
    }
}

/// Record usage for a Var node.
fn collect_var_usage(
    name: &str,
    ann: Option<&ExprSort>,
    in_bool_ctx: bool,
    usage: &mut HashMap<String, VarUsage>,
) {
    let entry = usage.entry(name.to_string()).or_default();
    if let Some(sort) = ann {
        if entry.annotation.is_none() || matches!(entry.annotation, Some(ExprSort::Int)) {
            entry.annotation = Some(sort.clone());
        }
    }
    if in_bool_ctx {
        entry.in_bool_context = true;
    }
}

fn collect_tuple_constructor_evidence(
    var_side: &PureExpr,
    tuple_side: &PureExpr,
    usage: &mut HashMap<String, VarUsage>,
) {
    let target_name = resolve_view_var_name(var_side, None)
        .or_else(|| extract_base_var(var_side).map(String::from));
    let Some(name) = target_name else {
        return;
    };
    let Some(arity) = extract_tuple_constructor_arity(tuple_side) else {
        return;
    };
    let entry = usage.entry(name).or_default();
    entry.tuple_arity = Some(
        entry
            .tuple_arity
            .map_or(arity, |current| current.max(arity)),
    );
}

fn collect_tuple_projection_evidence(
    receiver: &PureExpr,
    field_idx: usize,
    usage: &mut HashMap<String, VarUsage>,
) {
    let arity = field_idx + 1;
    let (target_name, direct) = if let Some(view_name) = resolve_view_var_name(receiver, None) {
        (Some(view_name), false)
    } else {
        (extract_base_var(receiver).map(String::from), true)
    };
    let Some(name) = target_name else {
        return;
    };
    let entry = usage.entry(name).or_default();
    entry.tuple_arity = Some(
        entry
            .tuple_arity
            .map_or(arity, |current| current.max(arity)),
    );
    if direct {
        entry.tuple_arity_from_direct_projection = true;
    }
}

/// Collect ADT constructor equality evidence from `var == Ctor(...)`.
///
/// When a variable appears in equality with a known Option/Result constructor
/// (Some/None/Ok/Err), record the constructor family so `determine_sort` can
/// assign the correct sort instead of falling back to Int. (#2700)
fn collect_constructor_equality_evidence(
    var_side: &PureExpr,
    ctor_side: &PureExpr,
    usage: &mut HashMap<String, VarUsage>,
) {
    let Some(name) = extract_base_var(var_side) else {
        return;
    };
    let Some(family) = extract_constructor_family(ctor_side) else {
        return;
    };
    usage
        .entry(name)
        .or_default()
        .constructor_family
        .get_or_insert(family);
}

/// Collect int-literal-equality evidence from `var == N` / `var != N` where
/// `N` is an integer literal outside {0, 1}.
///
/// Marks both the base variable name (peeling Deref/Final/Old/View — the same
/// descent `collect_names_as_bool` uses when minting heuristic Bool hints, so
/// the veto set exactly covers the mint set) and the view-derived `_view`
/// name when the var side is a View expression. (arc_and_rc sort-plan flake)
fn collect_int_literal_equality_evidence(
    var_side: &PureExpr,
    literal_side: &PureExpr,
    usage: &mut HashMap<String, VarUsage>,
) {
    if !is_out_of_range_int_literal(literal_side) {
        return;
    }
    if let Some(view_name) = resolve_view_var_name(var_side, None) {
        usage.entry(view_name).or_default().int_literal_eq = true;
    }
    if let Some(name) = extract_base_var(var_side) {
        usage.entry(name).or_default().int_literal_eq = true;
    }
}

/// `true` for integer literals outside {0, 1} (peeling `Old` wrappers and
/// negation). Bool-vs-{0,1} equalities are legitimately encodable through
/// ay's 0/1 bridge, so only out-of-range literals constitute anti-Bool
/// evidence.
pub(in crate::encoder::sort_context) fn is_out_of_range_int_literal(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Int(n) => *n != 0 && *n != 1,
        // Negative literals arrive as UnOp(Neg, Int(n)); -1 and any -n (n>0)
        // are out of range, -0 == 0 is not.
        PureExpr::UnOp(UnOp::Neg, inner) => matches!(inner.as_ref(), PureExpr::Int(n) if *n != 0),
        PureExpr::Old(inner) => is_out_of_range_int_literal(inner),
        _ => false,
    }
}

/// Extract the ADT constructor family name from an expression.
///
/// Recognizes Option constructors (Some, None) and Result constructors (Ok, Err).
/// Peels through Deref/Final/Old/View wrappers. (#2700)
fn extract_constructor_family(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::LogicFnCall { name, .. } => match name.as_str() {
            "Some" | "None" => Some("Option".to_string()),
            "Ok" | "Err" => Some("Result".to_string()),
            _ => None,
        },
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => extract_constructor_family(inner),
        _ => None,
    }
}

fn extract_tuple_constructor_arity(expr: &PureExpr) -> Option<usize> {
    match expr {
        PureExpr::LogicFnCall { name, .. } => tuple_logic_fn_arity(name),
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => extract_tuple_constructor_arity(inner),
        PureExpr::Ite(_, then_expr, else_expr) => {
            let then_arity = extract_tuple_constructor_arity(then_expr);
            let else_arity = extract_tuple_constructor_arity(else_expr);
            match (then_arity, else_arity) {
                (Some(left), Some(right)) if left == right => Some(left),
                (Some(arity), None) | (None, Some(arity)) => Some(arity),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Extract the base variable name from an expression, peeling through
/// Deref/Final/Old/View wrappers. Delegates to `extract_base_var_name`
/// and converts to owned String. (#2654)
fn extract_base_var(expr: &PureExpr) -> Option<String> {
    super::extract_base_var_name(expr).map(String::from)
}

/// Determine the final ay Sort for a variable from all collected evidence.
/// Priority: quantifier > tuple equality/projection > annotation >
/// constructor equality > method evidence > view+method > bool > Int.
pub(crate) fn determine_sort(usage: &VarUsage) -> ay_dpll::api::Sort {
    use ay_dpll::api::Sort;

    // Priority 1: Quantifier-bound sort.
    if let Some(ref qs) = usage.quantifier_sort {
        let sort = expr_sort_to_ay_sort(qs);
        if sort != Sort::Int {
            return sort;
        }
    }

    // Priority 2: Tuple constructor / projection evidence.
    if let Some(arity) = usage.tuple_arity {
        return Sort::Uninterpreted(format!("Tuple{arity}"));
    }

    // Priority 3: Non-Int ExprSort annotation from MIR.
    if let Some(ref ann) = usage.annotation {
        let sort = expr_sort_to_ay_sort(ann);
        if sort != Sort::Int {
            return sort;
        }
    }

    // Priority 4: ADT constructor equality evidence. (#2700)
    // When `var == Some(...)` / `var == Err(...)` etc. appears in preconditions,
    // declare the variable with the constructor's sort family (OptionInt/ResultIntInt)
    // instead of defaulting to Int. Without this, sort coercion creates fresh
    // unconstrained constants that break the constraint propagation between
    // preconditions and the assertion.
    if let Some(ref family) = usage.constructor_family {
        match family.as_str() {
            "Option" => return Sort::Uninterpreted("OptionInt".to_string()),
            "Result" => return Sort::Uninterpreted("ResultIntInt".to_string()),
            _ => {}
        }
    }

    // Priority 5: Method call evidence.
    let has_seq_method = usage.method_calls.iter().any(|m| is_seq_only_method(m));
    let has_fmap_method = usage
        .method_calls
        .iter()
        .any(|m| matches!(m.as_str(), "lookup" | "merge"));
    if has_seq_method {
        return Sort::seq(Sort::Int);
    }
    if has_fmap_method {
        return Sort::Uninterpreted("FMap".to_string());
    }

    // Note: has_view alone is NOT Seq evidence. View is identity for scalars
    // (i32@ = Int) and only means Seq for collection types. The existing hint
    // cascade handles _view name variants; we only use has_view as Seq evidence
    // when combined with method calls on the same variable.
    if usage.has_view
        && usage.method_calls.iter().any(|m| {
            matches!(
                m.as_str(),
                "len" | "len_ghost" | "index" | "index_logic" | "get" | "set" | "push_back"
            )
        })
    {
        return Sort::seq(Sort::Int);
    }

    // Priority 6: Boolean context (unless has ambiguous methods like len
    // which could mean Seq).
    let has_ambiguous_method = usage.method_calls.iter().any(|m| {
        matches!(
            m.as_str(),
            "len" | "len_ghost" | "index" | "index_logic" | "get" | "set"
        )
    });
    // Int-literal-equality evidence vetoes the Bool inference: a variable
    // compared (Eq/Ne) to a literal outside {0,1} cannot be Bool under a
    // faithful encoding — freezing it Bool forces the equality premise to be
    // fabricated away (`__trust_wp_unencodable_eq_*`), producing false
    // counterexamples. (arc_and_rc sort-plan flake)
    if usage.in_bool_context && !has_ambiguous_method && !usage.int_literal_eq {
        return Sort::Bool;
    }

    // Default: Int.
    Sort::Int
}

#[cfg(test)]
mod tests;
