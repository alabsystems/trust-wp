// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::HashMap,
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use trust_wp_driver::builtin_trust_wp_std_specs;

use super::*;

static CLONE_PIPELINE_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

struct StdSpecExtractCallbacks {
    fn_name: String,
    return_expr: Option<PureExpr>,
    assumptions: Option<Vec<PureExpr>>,
    ran: bool,
}

impl Callbacks for StdSpecExtractCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let arg_names = resolve_arg_names_or_warn(tcx, local_def_id.to_def_id(), None);
            let user_specs = HashMap::new();
            let trait_specs = HashMap::new();
            let extern_specs = builtin_trust_wp_std_specs();

            let (expr, effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &user_specs,
                &trait_specs,
                &extern_specs,
            );
            self.return_expr = expr;
            self.assumptions = Some(effects.assumptions);
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn extract_with_std_specs(source: &str, fn_name: &str) -> (Option<PureExpr>, Vec<PureExpr>) {
    let unique = CLONE_PIPELINE_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_clone_pipeline_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_clone_pipeline_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = StdSpecExtractCallbacks {
        fn_name: fn_name.to_string(),
        return_expr: None,
        assumptions: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract std-spec return expr and assumptions for `{fn_name}`"
    );
    (
        callbacks.return_expr,
        callbacks
            .assumptions
            .expect("assumptions should be set when ran=true"),
    )
}

fn clone_receiver_is_self0(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(name, _) => name == "self.0",
        PureExpr::LogicFnCall { name, args } => {
            name == "__trust_wp_tuple_get_0"
                && matches!(args.as_slice(), [PureExpr::Var(base, _)] if base == "self")
        }
        _ => false,
    }
}

fn expr_contains_ok_result(expr: &PureExpr, clone_results: &[&str]) -> bool {
    match expr {
        PureExpr::Var(..) | PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => false,
        PureExpr::Deref(inner)
        | PureExpr::View(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::UnOp(_, inner) => expr_contains_ok_result(inner, clone_results),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_contains_ok_result(cond, clone_results)
                || expr_contains_ok_result(then_expr, clone_results)
                || expr_contains_ok_result(else_expr, clone_results)
        }
        PureExpr::Let { value, body, .. } => {
            expr_contains_ok_result(value, clone_results)
                || expr_contains_ok_result(body, clone_results)
        }
        PureExpr::LetAssume { assumption, body } => {
            expr_contains_ok_result(assumption, clone_results)
                || expr_contains_ok_result(body, clone_results)
        }
        PureExpr::LetObligation { obligation, body } => {
            expr_contains_ok_result(obligation, clone_results)
                || expr_contains_ok_result(body, clone_results)
        }
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_contains_ok_result(lhs, clone_results)
                || expr_contains_ok_result(rhs, clone_results)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_contains_ok_result(receiver, clone_results)
                || args
                    .iter()
                    .any(|arg| expr_contains_ok_result(arg, clone_results))
        }
        PureExpr::LogicFnCall { name, args } => {
            name == "OwnResult::Ok"
                && matches!(
                    args.as_slice(),
                    [PureExpr::Var(result_name, _)]
                        if clone_results.contains(&result_name.as_str())
                )
                || args
                    .iter()
                    .any(|arg| expr_contains_ok_result(arg, clone_results))
        }
        PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => {
            expr_contains_ok_result(body, clone_results)
        }
        PureExpr::Match { scrutinee, arms } => {
            expr_contains_ok_result(scrutinee, clone_results)
                || arms
                    .iter()
                    .any(|arm| expr_contains_ok_result(&arm.body, clone_results))
        }
        PureExpr::Closure { body, .. } => expr_contains_ok_result(body, clone_results),
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => panic!("unhandled PureExpr variant"),
    }
}

#[test]
fn own_result_cloned_pipeline_uses_scalar_clone_assumption_result() {
    let source = r#"
pub enum OwnResult<T, E> {
    Ok(T),
    Err(E),
}

impl<T, E> OwnResult<&T, E> {
    pub fn cloned(self) -> OwnResult<T, E>
    where
        T: Clone,
    {
        match self {
            OwnResult::Ok(t) => OwnResult::Ok(t.clone()),
            OwnResult::Err(e) => OwnResult::Err(e),
        }
    }
}
"#;

    let (return_expr, assumptions) = extract_with_std_specs(source, "cloned");

    // The clone runs on the `Ok` arm only, so its postcondition is scoped to
    // that arm's edge (`edge ==> post`); the post is read under the guard.
    let clone_assumptions: Vec<(&PureExpr, &str)> = assumptions
        .iter()
        .map(|assumption| match assumption {
            PureExpr::BinOp(_, trust_wp_core::formula::BinOp::Implies, post) => post.as_ref(),
            unguarded => unguarded,
        })
        .filter_map(|assumption| match assumption {
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } if method == "postcondition"
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "T::clone") =>
            {
                match args.as_slice() {
                    [input, PureExpr::Var(result_name, _)]
                        if clone_receiver_is_self0(input) && result_name.starts_with("$call_") =>
                    {
                        Some((assumption, result_name.as_str()))
                    }
                    _ => None,
                }
            }
            _ => None,
        })
        .collect();

    assert!(
        !clone_assumptions.is_empty(),
        "expected `OwnResult<&T, E>::cloned` to emit a scalar \
         `T::clone.postcondition(self.0, call_N)` assumption, got {assumptions:?}"
    );
    assert!(
        clone_assumptions.iter().all(|(assumption, _)| {
            !matches!(
                assumption,
                PureExpr::MethodCall { args, .. }
                    if matches!(
                        args.first(),
                        Some(PureExpr::LogicFnCall { name, .. }) if name == "__trust_wp_tuple1"
                    )
            )
        }),
        "singleton tuple sugar should already be desugared before the clone assumption reaches the \
         driver effects list: {clone_assumptions:?}"
    );

    let return_expr = return_expr.expect("expected `cloned` to extract a return expression");
    let clone_results: Vec<&str> = clone_assumptions
        .iter()
        .map(|(_, result_name)| *result_name)
        .collect();
    assert!(
        expr_contains_ok_result(&return_expr, &clone_results),
        "the lowered return expr should contain `OwnResult::Ok(call_N)` using the same synthesized result \
         named by the clone postcondition assumption, got {return_expr:?}"
    );
}

/// s34: a non-deref field write on a by-value local updates the local's whole
/// value (functional update); the returned value reflects the write.
#[test]
fn s34_local_field_write_updates_whole_value() {
    let (expr, _) = extract_with_std_specs(
        "pub fn f() -> (u64, u64) { let mut p = (1u64, 2u64); p.0 = 5; p }",
        "f",
    );
    assert_eq!(
        expr.map(|e| e.to_string()).as_deref(),
        Some("__trust_wp_tuple2(5, 2)"),
        "returned tuple must reflect `p.0 = 5`"
    );
}

/// s34: a field write on a by-value PARAMETER never returns the entry symbol
/// and never states a write fact over it.
#[test]
fn s34_param_field_write_never_returns_entry_symbol() {
    let (expr, _) = extract_with_std_specs(
        "pub fn f(mut t: (u64, u64)) -> (u64, u64) { t.0 = 7; t }",
        "f",
    );
    let rendered = expr.map(|e| e.to_string()).unwrap_or_default();
    assert!(
        rendered.contains("__trust_wp_tuple2(7, __trust_wp_tuple_get_1(t))"),
        "expected functional update over the entry value, got `{rendered}`"
    );
    assert!(
        !rendered.contains("__trust_wp_tuple_get_0(t) == 7"),
        "no write fact over the parameter entry symbol: `{rendered}`"
    );
}

/// s34: an arity-1 carrier write cannot be represented exactly: the local is
/// rebound to a fresh symbol, never the stale entry value `s`.
#[test]
fn s34_single_field_write_havocs_local() {
    let (expr, _) = extract_with_std_specs(
        "pub struct S(pub u64);\npub fn f(mut s: S) -> S { s.0 = 7; s }",
        "f",
    );
    let rendered = expr.map(|e| e.to_string()).unwrap_or_default();
    assert!(
        rendered.contains("$havoc_local_"),
        "expected a fresh havoc symbol, got `{rendered}`"
    );
}

/// s34: a mutating call through a field borrow of a by-value arity-1 owner
/// never leaves the owner at its pre-call value.
#[test]
fn s34_field_borrow_call_does_not_keep_owner_pre_state() {
    let (expr, _) = extract_with_std_specs(
        "pub struct W(pub Vec<u64>);\npub fn f(mut w: W) -> W { w.0.push(7); w }",
        "f",
    );
    let rendered = expr.map(|e| e.to_string()).unwrap_or_default();
    assert_ne!(rendered, "w", "owner kept its entry value");
    assert!(
        rendered.contains("$havoc_owner_") || rendered.contains("^"),
        "expected an advanced or havocked owner, got `{rendered}`"
    );
}
