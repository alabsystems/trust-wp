// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Leading-call extraction for `proof_assert!` closures.
//!
//! `proof_assert! { lemma(); assertion }` stores only the trailing expression in
//! the doc marker text. To recover lemma postconditions we inspect the HIR
//! closure body directly, collect leading call statements, and instantiate the
//! called function's `#[ensures]` clauses with the actual arguments.

use std::collections::{HashMap, HashSet};

use rustc_hir::{def_id::DefId, Expr, ExprKind, Stmt, StmtKind};
use rustc_middle::ty::{TyCtxt, TyKind, TypeckResults};
use trust_wp_core::{
    contract_parser::{parse_contract, parse_contract_body_with_leading_exprs},
    formula::{BinOp, PureExpr},
    logic::LogicFnDef,
};
use trust_wp_driver::StdSpec;

use super::{
    contract_rewrite::rewrite_logic_method_calls_expr,
    helpers::contains_mutating_call_effect,
    logic_fn_scope::{build_logic_fn_path_map, normalize_logic_fn_names},
    parsing::get_arg_names_from_def_id,
    proof_assert_extract::{collapse_idempotent_views, normalize_view_fn_calls},
};

/// Collect assumptions from leading call statements in a `proof_assert!` body.
///
/// Calls are recognized only while scanning the contiguous statement prefix of
/// the closure body. This matches the `proof_assert! { lemma(); lemma(); expr }`
/// pattern used by Creusot/RustHorn. Preconditions guard the instantiated
/// postcondition; `result`-dependent postconditions are skipped here.
pub(super) fn collect_leading_proof_assert_assumptions(
    tcx: TyCtxt<'_>,
    proof_assert: &crate::proof_assert::ProofAssert,
    logic_fn_defs: &[LogicFnDef],
    user_specs: &HashMap<DefId, StdSpec>,
    logic_method_names: &HashSet<String>,
) -> (Vec<PureExpr>, bool) {
    let Some(closure_local_def_id) = proof_assert.closure_def_id.and_then(DefId::as_local) else {
        return (Vec::new(), false);
    };
    let Some(body_id) = tcx.hir_node_by_def_id(closure_local_def_id).body_id() else {
        return (Vec::new(), false);
    };
    let hir_body = tcx.hir_body(body_id);
    let ExprKind::Block(block, _) = hir_body.value.kind else {
        return (Vec::new(), false);
    };

    let typeck_results = tcx.typeck(closure_local_def_id);
    let logic_fn_path_map = build_logic_fn_path_map(logic_fn_defs);
    let mut assumptions = Vec::new();
    let mut has_mutating_call_effect = false;

    for stmt in block.stmts {
        let Some(expr) = stmt_expr(stmt) else {
            break;
        };
        let Some(call) = extract_call(typeck_results, expr) else {
            break;
        };
        let Some(spec) = user_specs.get(&call.def_id) else {
            continue;
        };
        let Some(actual_args) = parse_actual_args(tcx, &call.arguments) else {
            continue;
        };
        let (instantiated, mutating) = instantiate_logic_spec_ensures(
            tcx,
            call.def_id,
            spec,
            &actual_args,
            &logic_fn_path_map,
            logic_method_names,
        );
        assumptions.extend(instantiated);
        has_mutating_call_effect |= mutating;
    }

    if assumptions.is_empty() {
        if let Some(expr_text) = proof_assert.expr_text.as_deref() {
            let (fallback_assumptions, mutating) = collect_text_fallback_assumptions(
                tcx,
                expr_text,
                logic_fn_defs,
                user_specs,
                logic_method_names,
            );
            assumptions.extend(fallback_assumptions);
            has_mutating_call_effect |= mutating;
        }
    }

    (assumptions, has_mutating_call_effect)
}

struct ResolvedCall<'tcx> {
    def_id: DefId,
    arguments: Vec<&'tcx Expr<'tcx>>,
}

fn stmt_expr<'tcx>(stmt: &'tcx Stmt<'tcx>) -> Option<&'tcx Expr<'tcx>> {
    match stmt.kind {
        StmtKind::Expr(expr) | StmtKind::Semi(expr) => Some(expr),
        _ => None,
    }
}

fn extract_call<'tcx>(
    typeck_results: &'tcx TypeckResults<'tcx>,
    expr: &'tcx Expr<'tcx>,
) -> Option<ResolvedCall<'tcx>> {
    match peel_expr(expr).kind {
        ExprKind::MethodCall(_, receiver, args, _) => {
            let expr = peel_expr(expr);
            let def_id = typeck_results.type_dependent_def_id(expr.hir_id)?;
            let mut arguments = Vec::with_capacity(1 + args.len());
            arguments.push(receiver);
            arguments.extend(args.iter());
            Some(ResolvedCall { def_id, arguments })
        }
        ExprKind::Call(callee, args) => {
            let def_id = call_def_id(typeck_results, callee)?;
            Some(ResolvedCall {
                def_id,
                arguments: args.iter().collect(),
            })
        }
        _ => None,
    }
}

fn call_def_id(typeck_results: &TypeckResults<'_>, callee: &Expr<'_>) -> Option<DefId> {
    if let TyKind::FnDef(def_id, _) = typeck_results.expr_ty(callee).kind() {
        return Some(*def_id);
    }

    if let ExprKind::Path(qpath) = &callee.kind {
        if let rustc_hir::def::Res::Def(_, def_id) = typeck_results.qpath_res(qpath, callee.hir_id)
        {
            return Some(def_id);
        }
    }

    None
}

fn parse_actual_args(tcx: TyCtxt<'_>, args: &[&Expr<'_>]) -> Option<Vec<PureExpr>> {
    args.iter()
        .map(|expr| parse_expr_snippet(tcx, expr))
        .collect()
}

fn instantiate_logic_spec_ensures(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    spec: &StdSpec,
    actual_args: &[PureExpr],
    logic_fn_path_map: &HashMap<String, String>,
    logic_method_names: &HashSet<String>,
) -> (Vec<PureExpr>, bool) {
    let Some(param_names) = get_arg_names_from_def_id(tcx, def_id) else {
        return (Vec::new(), false);
    };
    if param_names.len() != actual_args.len() {
        return (Vec::new(), false);
    }

    let substitutions: HashMap<String, PureExpr> = param_names
        .iter()
        .cloned()
        .zip(actual_args.iter().cloned())
        .collect();

    // Normalize an instantiated contract clause identically for `requires` and
    // `ensures` so the precondition guard's terms line up with the assertion /
    // loop-invariant terms it must cancel against.
    let normalize = |clause: PureExpr| -> PureExpr {
        let expr = clause.substitute(&substitutions);
        let expr = normalize_view_fn_calls(expr);
        let expr = collapse_idempotent_views(expr);
        let expr = normalize_logic_fn_names(expr, logic_fn_path_map);
        rewrite_logic_method_calls_expr(&expr, logic_method_names)
    };

    // Build the precondition guard for lemmas that carry `#[requires]`.
    //
    // A logic lemma's specification is the verified theorem
    // `forall params. (R_1 && .. && R_n) ==> E_i`. When the lemma has
    // preconditions we may therefore assume only the requires-GUARDED instance
    // `R(args) ==> E(args)` at the proof_assert call site — never the bare
    // `E(args)`. This guarded instance is a ground instance of a *proven*
    // theorem, so assuming it can never close an otherwise-invalid goal.
    //
    // The "proven" premise is enforced upstream: unverified logic functions
    // have their `ensures` cleared by `downgrade_unverified_logic_specs` before
    // this `user_specs` table is consulted, so reaching here with a non-empty
    // `ensures` means the postcondition obligation was discharged. If any
    // `requires` clause cannot be faithfully reconstructed (parse failure, or a
    // `result` reference that is meaningless in a precondition) we skip the
    // whole injection rather than emit a guard *weaker* than the true
    // precondition, which would over-strengthen `R ==> E` and be unsound.
    let mut guard_clauses: Vec<PureExpr> = Vec::with_capacity(spec.requires.len());
    for require in &spec.requires {
        let Ok(parsed) = parse_contract(require) else {
            return (Vec::new(), false);
        };
        if parsed.free_vars().contains("result") {
            return (Vec::new(), false);
        }
        guard_clauses.push(normalize(parsed));
    }
    let guard: Option<PureExpr> = guard_clauses.into_iter().reduce(|acc, clause| {
        PureExpr::BinOp(
            std::sync::Arc::new(acc),
            BinOp::And,
            std::sync::Arc::new(clause),
        )
    });

    let has_mutating_call_effect = spec
        .ensures
        .iter()
        .filter_map(|ensure| parse_contract(ensure).ok())
        .any(|ensure| contains_mutating_call_effect(&ensure));

    let assumptions = spec
        .ensures
        .iter()
        .filter_map(|ensure| parse_contract(ensure).ok())
        .filter(|ensure| !ensure.free_vars().contains("result"))
        .map(|ensure| {
            let ensure = normalize(ensure);
            match &guard {
                Some(guard) => PureExpr::BinOp(
                    std::sync::Arc::new(guard.clone()),
                    BinOp::Implies,
                    std::sync::Arc::new(ensure),
                ),
                None => ensure,
            }
        })
        .collect();
    (assumptions, has_mutating_call_effect)
}

fn peel_expr<'tcx>(expr: &'tcx Expr<'tcx>) -> &'tcx Expr<'tcx> {
    match expr.kind {
        ExprKind::DropTemps(inner) => peel_expr(inner),
        ExprKind::Block(block, _) if block.stmts.is_empty() => block.expr.map_or(expr, peel_expr),
        _ => expr,
    }
}

fn parse_expr_snippet(tcx: TyCtxt<'_>, expr: &Expr<'_>) -> Option<PureExpr> {
    let expr = peel_expr(expr);
    let source_map = tcx.sess.source_map();
    let spans = [expr.span, expr.span.source_callsite()];
    for span in spans {
        let Ok(snippet) = source_map.span_to_snippet(span) else {
            continue;
        };
        if let Ok(parsed) = parse_contract(&snippet) {
            return Some(parsed);
        }
    }
    None
}

fn collect_text_fallback_assumptions(
    tcx: TyCtxt<'_>,
    expr_text: &str,
    logic_fn_defs: &[LogicFnDef],
    user_specs: &HashMap<DefId, StdSpec>,
    logic_method_names: &HashSet<String>,
) -> (Vec<PureExpr>, bool) {
    let Ok((leading_exprs, _)) = parse_contract_body_with_leading_exprs(expr_text) else {
        return (Vec::new(), false);
    };
    let logic_fn_path_map = build_logic_fn_path_map(logic_fn_defs);

    let mut assumptions = Vec::new();
    let mut has_mutating_call_effect = false;
    for expr in &leading_exprs {
        let (instantiated, mutating) = instantiate_text_call_ensures(
            tcx,
            expr,
            user_specs,
            logic_fn_defs,
            &logic_fn_path_map,
            logic_method_names,
        );
        assumptions.extend(instantiated);
        has_mutating_call_effect |= mutating;
    }
    (assumptions, has_mutating_call_effect)
}

fn instantiate_text_call_ensures(
    tcx: TyCtxt<'_>,
    expr: &PureExpr,
    user_specs: &HashMap<DefId, StdSpec>,
    logic_fn_defs: &[LogicFnDef],
    logic_fn_path_map: &HashMap<String, String>,
    logic_method_names: &HashSet<String>,
) -> (Vec<PureExpr>, bool) {
    let (fn_name, actual_args): (&str, Vec<PureExpr>) = match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            let mut all_args = Vec::with_capacity(1 + args.len());
            all_args.push((**receiver).clone());
            all_args.extend(args.clone());
            (method.as_str(), all_args)
        }
        PureExpr::LogicFnCall { name, args } => (name.as_str(), args.clone()),
        _ => return (Vec::new(), false),
    };

    let mut spec_matches = user_specs.iter().filter_map(|(def_id, spec)| {
        if !call_name_matches(tcx, *def_id, fn_name) {
            return None;
        }
        let param_names = get_arg_names_from_def_id(tcx, *def_id)?;
        if param_names.len() != actual_args.len() {
            return None;
        }
        Some((*def_id, spec))
    });
    if let Some((def_id, spec)) = spec_matches.next() {
        if spec_matches.next().is_none() {
            return instantiate_logic_spec_ensures(
                tcx,
                def_id,
                spec,
                &actual_args,
                logic_fn_path_map,
                logic_method_names,
            );
        }
    }

    let mut matches = logic_fn_defs.iter().filter(|logic_fn| {
        logic_fn.params().len() == actual_args.len() && logic_fn_name_matches(logic_fn, fn_name)
    });
    let Some(logic_fn) = matches.next() else {
        return (Vec::new(), false);
    };
    if matches.next().is_some() {
        return (Vec::new(), false);
    }

    instantiate_text_logic_fn_ensures(logic_fn, actual_args, logic_method_names)
}

/// Instantiate a text-fallback logic-function theorem at one call site.
///
/// The `logic_fn_defs` reaching this lane are the downstream catalog: an
/// unverified function has already been made opaque and had its `ensures`
/// cleared. For a verified function with preconditions, the theorem available
/// to callers is `requires(args) ==> ensures(args)`, never bare `ensures(args)`.
/// A malformed precondition fails closed by suppressing the whole injection.
fn instantiate_text_logic_fn_ensures(
    logic_fn: &LogicFnDef,
    actual_args: Vec<PureExpr>,
    logic_method_names: &HashSet<String>,
) -> (Vec<PureExpr>, bool) {
    if logic_fn.params().len() != actual_args.len() {
        return (Vec::new(), false);
    }

    let substitutions: HashMap<String, PureExpr> =
        logic_fn.params().iter().cloned().zip(actual_args).collect();
    let has_mutating_call_effect = logic_fn.ensures().iter().any(contains_mutating_call_effect);

    let mut guard_clauses = Vec::with_capacity(logic_fn.requires().len());
    for require in logic_fn.requires() {
        if require.free_vars().contains("result") {
            return (Vec::new(), false);
        }
        let require = require.substitute(&substitutions);
        guard_clauses.push(rewrite_logic_method_calls_expr(
            &require,
            logic_method_names,
        ));
    }
    let guard = guard_clauses.into_iter().reduce(|acc, clause| {
        PureExpr::BinOp(
            std::sync::Arc::new(acc),
            BinOp::And,
            std::sync::Arc::new(clause),
        )
    });

    let assumptions = logic_fn
        .ensures()
        .iter()
        .filter(|ensure| !ensure.free_vars().contains("result"))
        .map(|ensure| {
            let expr = ensure.substitute(&substitutions);
            let ensure = rewrite_logic_method_calls_expr(&expr, logic_method_names);
            match &guard {
                Some(guard) => PureExpr::BinOp(
                    std::sync::Arc::new(guard.clone()),
                    BinOp::Implies,
                    std::sync::Arc::new(ensure),
                ),
                None => ensure,
            }
        })
        .collect();
    (assumptions, has_mutating_call_effect)
}

fn call_name_matches(tcx: TyCtxt<'_>, def_id: DefId, call_name: &str) -> bool {
    let local_path = tcx.def_path_str(def_id);
    let short_name = local_path
        .rsplit("::")
        .next()
        .unwrap_or(local_path.as_str());
    if call_name == short_name || call_name == local_path {
        return true;
    }
    let crate_name = tcx.crate_name(def_id.krate);
    call_name == format!("{crate_name}::{local_path}")
}

fn logic_fn_name_matches(logic_fn: &LogicFnDef, call_name: &str) -> bool {
    call_name == logic_fn.name()
        || call_name == logic_fn.full_path()
        || logic_fn
            .full_path()
            .rsplit("::")
            .next()
            .is_some_and(|short_name| call_name == short_name)
}

#[cfg(test)]
mod tests {
    use std::{collections::HashSet, sync::Arc};

    use trust_wp_core::{
        formula::{BinOp, PureExpr},
        logic::LogicFnDef,
    };

    use super::instantiate_text_logic_fn_ensures;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn cmp(lhs: PureExpr, op: BinOp, rhs: PureExpr) -> PureExpr {
        PureExpr::BinOp(Arc::new(lhs), op, Arc::new(rhs))
    }

    #[test]
    fn text_fallback_guards_ensures_with_instantiated_requires() {
        let require = cmp(var("x"), BinOp::Gt, PureExpr::Int(0));
        let ensure = cmp(var("x"), BinOp::Gt, PureExpr::Int(1));
        let mut logic_fn = LogicFnDef::new_with_requires(
            "lemma".to_string(),
            "crate::lemma".to_string(),
            vec!["x".to_string()],
            vec![require],
            PureExpr::Bool(true),
        );
        logic_fn.set_ensures(vec![ensure]);

        let (assumptions, mutating) =
            instantiate_text_logic_fn_ensures(&logic_fn, vec![var("actual")], &HashSet::new());

        let expected = cmp(
            cmp(var("actual"), BinOp::Gt, PureExpr::Int(0)),
            BinOp::Implies,
            cmp(var("actual"), BinOp::Gt, PureExpr::Int(1)),
        );
        assert_eq!(assumptions, vec![expected]);
        assert!(!mutating);
    }

    #[test]
    fn text_fallback_rejects_result_dependent_precondition() {
        let mut logic_fn = LogicFnDef::new_with_requires(
            "bad".to_string(),
            "crate::bad".to_string(),
            vec![],
            vec![var("result")],
            PureExpr::Bool(true),
        );
        logic_fn.set_ensures(vec![PureExpr::Bool(false)]);

        let (assumptions, mutating) =
            instantiate_text_logic_fn_ensures(&logic_fn, vec![], &HashSet::new());
        assert!(assumptions.is_empty());
        assert!(!mutating);
    }
}
