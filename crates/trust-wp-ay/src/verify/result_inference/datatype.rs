// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Option/Result datatype inference from postconditions.

use ay_dpll::api::Sort;
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};

use crate::encoder::{
    match_enc::{
        is_stdlib_enum_qualifier, normalize_constructor_name, short_constructor_name,
        MatchDatatypeKind,
    },
    sort_context::expr_sort_to_ay_sort,
};

#[derive(Debug, Clone, PartialEq, Eq)]
enum DatatypeCandidate {
    Target(MatchDatatypeKind),
    OptionUnknown,
}

/// Check whether any postcondition uses `result` as a match scrutinee with
/// Option/Result constructor patterns, requiring it to have Datatype sort.
///
/// When the body returns `Option<bool>` but MIR simplifies it to `Bool(true)`,
/// `infer_expr_sort(return_expr)` returns `Sort::Bool`, but the postcondition
/// `match result { Some(true) => true, _ => false }` needs `result` as a Datatype.
/// Returns the [`MatchDatatypeKind`] so the caller can construct the datatype
/// value for the body assertion. (#1055)
pub(crate) fn result_match_datatype_from_postcondition(
    ensures: &[PureExpr],
) -> Option<MatchDatatypeKind> {
    let mut inferred: Option<DatatypeCandidate> = None;

    for ensure in ensures {
        let candidate = expr_match_datatype_for_result(ensure)
            .map(DatatypeCandidate::Target)
            .or_else(|| expr_constructor_datatype_candidate_for_result(ensure));
        let Some(candidate) = candidate else {
            continue;
        };

        if !record_datatype_candidate(&mut inferred, candidate) {
            return None;
        }
    }

    inferred.map(DatatypeCandidate::into_target)
}

/// Check whether a single expression contains a `match result { ... }` with
/// datatype constructor patterns.
pub(crate) fn expr_match_datatype_for_result(expr: &PureExpr) -> Option<MatchDatatypeKind> {
    let mut inferred = None;
    expr.for_each_recursive(|node| {
        if inferred.is_some() {
            return;
        }
        let PureExpr::Match { scrutinee, arms } = node else {
            return;
        };
        if matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "result") {
            inferred = MatchDatatypeKind::from_arms(arms);
        }
    });
    inferred
}

pub(crate) fn option_datatype_from_constructor_expr(expr: &PureExpr) -> Option<MatchDatatypeKind> {
    option_datatype_candidate_from_result_shape(expr).map(DatatypeCandidate::into_target)
}

fn option_datatype_candidate_from_result_shape(expr: &PureExpr) -> Option<DatatypeCandidate> {
    match expr {
        PureExpr::LogicFnCall { .. } | PureExpr::Var(_, _) => {
            constructor_datatype_candidate(expr).filter(DatatypeCandidate::is_option)
        }
        PureExpr::Ite(_, then_expr, else_expr) => merge_option_datatype_candidates([
            option_datatype_candidate_from_result_shape(then_expr),
            option_datatype_candidate_from_result_shape(else_expr),
        ]),
        PureExpr::Match { arms, .. } => {
            let mut candidates = Vec::with_capacity(arms.len());
            for arm in arms {
                candidates.push(option_datatype_candidate_from_result_shape(&arm.body));
            }
            merge_option_datatype_candidates(candidates)
        }
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => option_datatype_candidate_from_result_shape(body),
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => option_datatype_candidate_from_result_shape(inner),
        _ => None,
    }
}

fn merge_option_datatype_candidates<I>(candidates: I) -> Option<DatatypeCandidate>
where
    I: IntoIterator<Item = Option<DatatypeCandidate>>,
{
    let mut inferred: Option<DatatypeCandidate> = None;
    for candidate in candidates {
        let candidate = candidate?;
        if !candidate.is_option() || !record_datatype_candidate(&mut inferred, candidate) {
            return None;
        }
    }
    inferred
}

/// Infer a datatype requirement from constructor equalities that reference `result`.
///
/// Examples:
/// - `result == Some(v)` / `result == None` => `OptionInt`
/// - `result == Ok(v)` / `result == Err(e)` => `ResultIntInt`
///
/// This complements `expr_match_datatype_for_result`, which only detects
/// `match result { ... }` shapes. Some contracts use equality-only encodings.
fn expr_constructor_datatype_candidate_for_result(expr: &PureExpr) -> Option<DatatypeCandidate> {
    let mut inferred: Option<DatatypeCandidate> = None;
    if collect_constructor_datatype_candidates(expr, &mut inferred) {
        inferred
    } else {
        None
    }
}

fn collect_constructor_datatype_candidates(
    expr: &PureExpr,
    inferred: &mut Option<DatatypeCandidate>,
) -> bool {
    let mut valid = true;
    expr.for_each_recursive(|node| {
        if !valid {
            return;
        }
        let PureExpr::BinOp(left, op, right) = node else {
            return;
        };
        if !matches!(op, BinOp::Eq | BinOp::Ne) {
            return;
        }
        if is_direct_result_binding(left)
            && constructor_datatype_candidate(right)
                .is_some_and(|kind| !record_datatype_candidate(inferred, kind))
        {
            valid = false;
            return;
        }
        if is_direct_result_binding(right)
            && constructor_datatype_candidate(left)
                .is_some_and(|kind| !record_datatype_candidate(inferred, kind))
        {
            valid = false;
        }
    });
    valid
}

fn is_direct_result_binding(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(name, _) => name == "result",
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => is_direct_result_binding(inner),
        _ => false,
    }
}

fn constructor_datatype_candidate(expr: &PureExpr) -> Option<DatatypeCandidate> {
    let (ctor_name, args): (&str, &[PureExpr]) = match expr {
        PureExpr::LogicFnCall { name, args } => (name.as_str(), args.as_slice()),
        PureExpr::Var(name, _) => {
            // Bare `None` can appear as a variable token in some parsed contracts.
            (name.as_str(), &[])
        }
        _ => return None,
    };

    let short = short_constructor_name(ctor_name);
    // Only classify as stdlib Option/Result when the qualifier matches.
    // User-defined enums with Ok/Err variants (e.g., OwnResult::Ok) must not
    // be misclassified as ResultIntInt. (#2462)
    if !is_stdlib_enum_qualifier(ctor_name, short) {
        return None;
    }

    match short {
        "Some" => Some(DatatypeCandidate::Target(option_candidate_for_args(args))),
        "None" => Some(DatatypeCandidate::OptionUnknown),
        "Ok" | "Err" => Some(DatatypeCandidate::Target(MatchDatatypeKind::ResultIntInt)),
        _ => None,
    }
}

fn option_candidate_for_args(args: &[PureExpr]) -> MatchDatatypeKind {
    args.first()
        .and_then(non_int_payload_sort_hint)
        .map(MatchDatatypeKind::OptionPayload)
        .unwrap_or(MatchDatatypeKind::OptionInt)
}

fn non_int_payload_sort_hint(expr: &PureExpr) -> Option<Sort> {
    let sort = match expr {
        PureExpr::Var(_, Some(sort)) => expr_sort_hint(sort),
        PureExpr::LogicFnCall { name, .. } => user_constructor_payload_sort(name),
        PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => non_int_payload_sort_hint(inner),
        PureExpr::Ite(_, then_expr, else_expr) => {
            let then_sort = non_int_payload_sort_hint(then_expr)?;
            let else_sort = non_int_payload_sort_hint(else_expr)?;
            (then_sort == else_sort).then_some(then_sort)
        }
        _ => None,
    }?;
    (sort != Sort::Int).then_some(sort)
}

fn expr_sort_hint(sort: &ExprSort) -> Option<Sort> {
    let ay_sort = expr_sort_to_ay_sort(sort);
    (ay_sort != Sort::Int).then_some(ay_sort)
}

fn user_constructor_payload_sort(name: &str) -> Option<Sort> {
    let normalized = normalize_constructor_name(name);
    let short = short_constructor_name(normalized);
    if is_stdlib_enum_qualifier(normalized, short) {
        return None;
    }
    let qualifier = normalized.rsplit_once("::")?.0;
    let bare = qualifier
        .rsplit_once("::")
        .map_or(qualifier, |(_, name)| name);
    (!bare.is_empty()).then(|| Sort::Uninterpreted(bare.to_string()))
}

impl DatatypeCandidate {
    fn into_target(self) -> MatchDatatypeKind {
        match self {
            Self::Target(target) => target,
            Self::OptionUnknown => MatchDatatypeKind::OptionInt,
        }
    }

    fn is_option(&self) -> bool {
        match self {
            Self::Target(target) => is_option_target(target),
            Self::OptionUnknown => true,
        }
    }
}

fn record_datatype_candidate(
    inferred: &mut Option<DatatypeCandidate>,
    candidate: DatatypeCandidate,
) -> bool {
    let Some(existing) = inferred else {
        *inferred = Some(candidate);
        return true;
    };

    match (&*existing, candidate) {
        (DatatypeCandidate::OptionUnknown, DatatypeCandidate::OptionUnknown) => true,
        (DatatypeCandidate::OptionUnknown, DatatypeCandidate::Target(target))
            if is_option_target(&target) =>
        {
            *existing = DatatypeCandidate::Target(target);
            true
        }
        (DatatypeCandidate::Target(existing_target), DatatypeCandidate::OptionUnknown)
            if is_option_target(existing_target) =>
        {
            true
        }
        (
            DatatypeCandidate::Target(existing_target),
            DatatypeCandidate::Target(candidate_target),
        ) => *existing_target == candidate_target,
        _ => false,
    }
}

fn is_option_target(target: &MatchDatatypeKind) -> bool {
    matches!(
        target,
        MatchDatatypeKind::OptionInt | MatchDatatypeKind::OptionPayload(_)
    )
}
