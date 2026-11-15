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
use rustc_middle::{
    mir::{ProjectionElem, StatementKind},
    ty::TyCtxt,
};
use trust_wp_core::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
    ExprSort,
};

use super::*;
use crate::mir_analysis::translate::ty_to_expr_sort_enriched;

static EXTRACT_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

struct ReturnExprCallbacks {
    fn_name: String,
    return_expr: Option<PureExpr>,
    ran: bool,
}

impl Callbacks for ReturnExprCallbacks {
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

            let (expr, _effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &user_specs,
                &trait_specs,
                &HashMap::new(),
            );
            self.return_expr = expr;
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn extract_return_expr_in_source(source: &str, fn_name: &str) -> Option<PureExpr> {
    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_non_recursive_extract_{}_{}",
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
        "trust_wp_non_recursive_extract_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = ReturnExprCallbacks {
        fn_name: fn_name.to_string(),
        return_expr: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract return expr for `{fn_name}`"
    );
    callbacks.return_expr
}

struct SpannedReturnExprCallbacks {
    fn_name: String,
    return_expr: Option<PureExpr>,
    ran: bool,
}

impl Callbacks for SpannedReturnExprCallbacks {
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

            self.return_expr = extract_return_expr_spanned(
                tcx,
                body,
                &arg_names,
                &user_specs,
                &trait_specs,
                &HashMap::new(),
            )
            .map(|expr| expr.expr);
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn extract_spanned_return_expr_in_source(source: &str, fn_name: &str) -> Option<PureExpr> {
    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_non_recursive_spanned_extract_{}_{}",
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
        "trust_wp_non_recursive_spanned_extract_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = SpannedReturnExprCallbacks {
        fn_name: fn_name.to_string(),
        return_expr: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract spanned return expr for `{fn_name}`"
    );
    callbacks.return_expr
}

struct ProgramPointStateCallbacks {
    fn_name: String,
    closure_parent_fn_name: String,
    spec: StdSpec,
    substitutions: Option<NameSubstitutions>,
    assumptions: Option<Vec<PureExpr>>,
    ran: bool,
}

impl Callbacks for ProgramPointStateCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let target_suffix = format!("::{}", self.fn_name);
        let closure_parent_suffix = format!("::{}", self.closure_parent_fn_name);
        let mut target_body_owner = None;
        let mut closure_def_id = None;

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path == self.fn_name || def_path.ends_with(&target_suffix) {
                target_body_owner = Some(local_def_id);
            }
            if tcx.def_kind(local_def_id) == rustc_hir::def::DefKind::Closure
                && (def_path.starts_with(&format!("{}::{{closure", self.closure_parent_fn_name))
                    || def_path.contains(&format!("{closure_parent_suffix}::{{closure")))
            {
                closure_def_id = Some(local_def_id.to_def_id());
            }
        }

        let target_body_owner = target_body_owner.expect("target function not found");
        let closure_def_id = closure_def_id.expect("closure def_id not found");

        let body = tcx.optimized_mir(target_body_owner.to_def_id());
        let arg_names = resolve_arg_names_or_warn(tcx, target_body_owner.to_def_id(), None);
        let mut user_specs = HashMap::new();
        user_specs.insert(closure_def_id, self.spec.clone());

        let after_local = body
            .var_debug_info
            .iter()
            .find_map(|info| {
                (info.name.as_str() == "after").then(|| match info.value {
                    rustc_middle::mir::VarDebugInfoContents::Place(place)
                        if place.projection.is_empty() =>
                    {
                        Some(place.local)
                    }
                    _ => None,
                })?
            })
            .expect("debug local for `after` not found");

        let stop_location = body
            .basic_blocks
            .iter_enumerated()
            .find_map(|(bb, bb_data)| {
                bb_data
                    .statements
                    .iter()
                    .enumerate()
                    .find_map(|(idx, stmt)| match &stmt.kind {
                        StatementKind::Assign((place, _))
                            if place.local == after_local && place.projection.is_empty() =>
                        {
                            Some(rustc_middle::mir::Location {
                                block: bb,
                                statement_index: idx,
                            })
                        }
                        _ => None,
                    })
            })
            .expect("assignment to `after` not found");

        let state = extract_program_point_state_until_location_detailed(
            tcx,
            body,
            &arg_names,
            &user_specs,
            &HashMap::new(),
            &HashMap::new(),
            stop_location,
        );
        self.substitutions = Some(state.substitutions);
        self.assumptions = Some(state.call_effects.assumptions);
        self.ran = true;
        Compilation::Stop
    }
}

fn extract_program_point_state_with_closure_user_spec(
    source: &str,
    fn_name: &str,
    spec: StdSpec,
) -> (NameSubstitutions, Vec<PureExpr>) {
    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_program_point_state_{}_{}",
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
        "trust_wp_program_point_state_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = ProgramPointStateCallbacks {
        fn_name: fn_name.to_string(),
        closure_parent_fn_name: fn_name.to_string(),
        spec,
        substitutions: None,
        assumptions: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract program-point state for `{fn_name}`"
    );
    (
        callbacks
            .substitutions
            .expect("substitutions should be set when ran=true"),
        callbacks
            .assumptions
            .expect("assumptions should be set when ran=true"),
    )
}

fn expr_contains_ite(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Ite(_, _, _) => true,
        PureExpr::LetAssume { body, .. } => expr_contains_ite(body),
        PureExpr::Let { value, body, .. } => expr_contains_ite(value) || expr_contains_ite(body),
        _ => false,
    }
}

fn expr_contains_method_call(expr: &PureExpr, expected: &str) -> bool {
    match expr {
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Var(..) => false,
        PureExpr::Deref(inner)
        | PureExpr::View(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::UnOp(_, inner) => expr_contains_method_call(inner, expected),
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_contains_method_call(lhs, expected) || expr_contains_method_call(rhs, expected)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_contains_method_call(cond, expected)
                || expr_contains_method_call(then_expr, expected)
                || expr_contains_method_call(else_expr, expected)
        }
        PureExpr::Let { value, body, .. } => {
            expr_contains_method_call(value, expected) || expr_contains_method_call(body, expected)
        }
        PureExpr::LetAssume {
            assumption, body, ..
        } => {
            expr_contains_method_call(assumption, expected)
                || expr_contains_method_call(body, expected)
        }
        PureExpr::LetObligation {
            obligation, body, ..
        } => {
            expr_contains_method_call(obligation, expected)
                || expr_contains_method_call(body, expected)
        }
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            method == expected
                || expr_contains_method_call(receiver, expected)
                || args
                    .iter()
                    .any(|arg| expr_contains_method_call(arg, expected))
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter()
            .any(|arg| expr_contains_method_call(arg, expected)),
        PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => {
            expr_contains_method_call(body, expected)
        }
        PureExpr::Match { scrutinee, arms } => {
            expr_contains_method_call(scrutinee, expected)
                || arms
                    .iter()
                    .any(|arm| expr_contains_method_call(&arm.body, expected))
        }
        PureExpr::Closure { body, .. } => expr_contains_method_call(body, expected),
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => panic!("unhandled PureExpr variant"),
    }
}

fn expr_contains_var_named(expr: &PureExpr, expected: &str) -> bool {
    match expr {
        PureExpr::Var(name, _) => name == expected,
        PureExpr::Bool(_) | PureExpr::Int(_) => false,
        PureExpr::Deref(inner)
        | PureExpr::View(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::UnOp(_, inner) => expr_contains_var_named(inner, expected),
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_contains_var_named(lhs, expected) || expr_contains_var_named(rhs, expected)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_contains_var_named(cond, expected)
                || expr_contains_var_named(then_expr, expected)
                || expr_contains_var_named(else_expr, expected)
        }
        PureExpr::Let { value, body, .. } => {
            expr_contains_var_named(value, expected) || expr_contains_var_named(body, expected)
        }
        PureExpr::LetAssume {
            assumption, body, ..
        } => {
            expr_contains_var_named(assumption, expected) || expr_contains_var_named(body, expected)
        }
        PureExpr::LetObligation {
            obligation, body, ..
        } => {
            expr_contains_var_named(obligation, expected) || expr_contains_var_named(body, expected)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_contains_var_named(receiver, expected)
                || args
                    .iter()
                    .any(|arg| expr_contains_var_named(arg, expected))
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter()
            .any(|arg| expr_contains_var_named(arg, expected)),
        PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => {
            expr_contains_var_named(body, expected)
        }
        PureExpr::Match { scrutinee, arms } => {
            expr_contains_var_named(scrutinee, expected)
                || arms
                    .iter()
                    .any(|arm| expr_contains_var_named(&arm.body, expected))
        }
        PureExpr::Closure { body, .. } => expr_contains_var_named(body, expected),
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => panic!("unhandled PureExpr variant"),
    }
}

#[test]
fn top_level_const_return_extracts_literal_value() {
    let source = r#"
const FOO: usize = 42;

pub const fn foo() -> usize {
    FOO
}
"#;

    let expr = extract_return_expr_in_source(source, "foo");
    assert_eq!(
        expr,
        Some(PureExpr::Int(42)),
        "top-level const returns should extract to the literal value",
    );
}

#[test]
fn inline_const_generic_return_extracts_symbolic_const_param() {
    let source = r#"
pub const fn add_one<const N: usize>() -> usize {
    const { N + 1 }
}
"#;

    let expr = extract_return_expr_in_source(source, "add_one")
        .expect("inline const generic returns should be extractable");
    assert!(
        expr_contains_var_named(&expr, "N"),
        "inline const generic extraction should retain the const parameter, got {expr:?}"
    );
}

#[test]
fn nested_checked_add_return_does_not_keep_tuple_get_artifact() {
    let source = r#"
pub fn triple(x: i32) -> i32 {
    x + x + x
}
"#;

    let expr = extract_return_expr_in_source(source, "triple")
        .expect("nested checked arithmetic return should extract");
    let mut contains_tuple_get = false;
    expr.for_each_recursive(|node| {
        if let PureExpr::LogicFnCall { name, .. } = node {
            if name == &tuple_field_logic_fn_name(0) {
                contains_tuple_get = true;
            }
        }
    });

    assert!(
        !contains_tuple_get,
        "checked arithmetic scalar return should not retain tuple_get_0 artifacts, got {expr:?}"
    );
}

#[test]
fn spanned_try_operator_extraction_matches_context_path() {
    let source = r#"
pub fn try_add_one(x: Option<i32>) -> Option<i32> {
    let y = x?;
    Some(y)
}
"#;

    let context_expr = extract_return_expr_in_source(source, "try_add_one")
        .expect("context extraction should handle simple try operators");
    let spanned_expr = extract_spanned_return_expr_in_source(source, "try_add_one")
        .expect("spanned extraction should handle simple try operators");

    assert_eq!(
        spanned_expr, context_expr,
        "spanned extraction should mirror the context extractor for `?` bodies"
    );
    // After reconstruction optimization (#2675), `let y = x?; Some(y)` simplifies
    // to just `x` because `Ite(is_some(x), Some(unwrap(x)), x)` is identity.
    assert!(
        matches!(&spanned_expr, PureExpr::Var(..)),
        "try extraction on reconstruction pattern should simplify to the input variable, got {spanned_expr:?}"
    );
}

#[test]
fn spanned_result_try_operator_extraction_matches_context_path() {
    let source = r#"
pub fn try_ok_identity(x: Result<i32, i32>) -> Result<i32, i32> {
    let y = x?;
    Ok(y)
}
"#;

    let context_expr = extract_return_expr_in_source(source, "try_ok_identity")
        .expect("context extraction should handle simple Result try operators");
    let spanned_expr = extract_spanned_return_expr_in_source(source, "try_ok_identity")
        .expect("spanned extraction should handle simple Result try operators");

    assert_eq!(
        spanned_expr, context_expr,
        "spanned extraction should mirror the context extractor for Result `?` bodies"
    );
    // After reconstruction optimization (#2675), `let y = x?; Ok(y)` simplifies
    // to just `x` because `Ite(is_ok(x), Ok(unwrap(x)), x)` is identity.
    assert!(
        matches!(&spanned_expr, PureExpr::Var(..)),
        "Result try extraction on reconstruction pattern should simplify to the input variable, got {spanned_expr:?}"
    );
}

#[test]
fn slice_first_match_extracts_non_none_body() {
    let source = r#"
pub fn slice_first<T>(a: &[T]) -> Option<&T> {
    if a.len() > 0 { Some(&a[0]) } else { None }
}
"#;

    let expr = extract_return_expr_in_source(source, "slice_first")
        .expect("slice_first should extract a body expression");
    assert!(
        expr_contains_ite(&expr),
        "slice_first extraction should preserve the branch structure, got {expr:?}"
    );
}

#[test]
fn index_mut_slice_return_extracts_index_logic_projection() {
    let source = r#"
pub fn index_mut_slice<T>(v: &mut [T]) -> &mut T {
    &mut v[12]
}
"#;

    let expr = extract_return_expr_in_source(source, "index_mut_slice")
        .expect("&mut [T] index returns should be extractable");
    assert!(
        expr_contains_method_call(&expr, "index_logic"),
        "&mut [T] index extraction should retain the index_logic projection, got {expr:?}"
    );
}

#[test]
fn index_mut_array_return_extracts_index_logic_projection() {
    let source = r#"
pub fn index_mut_array<T>(v: &mut [T; 31]) -> &mut T {
    &mut v[12]
}
"#;

    let expr = extract_return_expr_in_source(source, "index_mut_array")
        .expect("&mut [T; N] index returns should be extractable");
    assert!(
        expr_contains_method_call(&expr, "index_logic"),
        "&mut [T; N] index extraction should retain the index_logic projection, got {expr:?}"
    );
}

/// Const generic method on a generic struct: `own_params.zip(substs)` must skip
/// parent args so that the method's own const generic `M` is paired with its
/// actual substitution (5), not the parent's const generic `N` (3). (#2356)
#[test]
fn const_generic_method_on_generic_struct_extracts_own_const_param() {
    let source = r#"
pub struct Wrapper<const N: usize>;

impl<const N: usize> Wrapper<N> {
    #[inline(never)]
    pub fn method<const M: usize>(x: usize) -> usize {
        if x > 0 { M } else { N }
    }
}
pub fn caller(x: usize) -> usize {
    Wrapper::<3>::method::<5>(x)
}
"#;

    struct ConstGenericMethodCallbacks {
        param_names: Vec<String>,
        translated_exprs: Vec<PureExpr>,
        ran: bool,
    }

    impl Callbacks for ConstGenericMethodCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            use rustc_middle::mir::TerminatorKind;

            // Find the caller's MIR and locate the call to method<5>
            for local_def_id in tcx.hir_body_owners() {
                let path = tcx.def_path_str(local_def_id);
                if !path.ends_with("::caller") && path != "caller" {
                    continue;
                }

                let body = tcx.optimized_mir(local_def_id.to_def_id());
                for bb_data in body.basic_blocks.iter() {
                    let Some(terminator) = &bb_data.terminator else {
                        continue;
                    };
                    let TerminatorKind::Call { func, .. } = &terminator.kind else {
                        continue;
                    };

                    // Extract callee DefId from the func operand
                    let Operand::Constant(deref!(constant)) = func else {
                        continue;
                    };
                    let rustc_middle::ty::TyKind::FnDef(callee_def_id, _) = constant.ty().kind()
                    else {
                        continue;
                    };

                    let mut translated_args = Vec::new();
                    let mut param_names = Vec::new();
                    extend_call_with_const_generic_args(
                        tcx,
                        *callee_def_id,
                        func,
                        &mut translated_args,
                        &mut param_names,
                    );

                    self.param_names = param_names;
                    self.translated_exprs = translated_args.into_iter().map(|a| a.expr).collect();
                    self.ran = true;
                    return Compilation::Stop;
                }
            }
            Compilation::Stop
        }
    }

    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_const_generic_method_{}_{}",
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
        "trust_wp_const_generic_method_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = ConstGenericMethodCallbacks {
        param_names: Vec::new(),
        translated_exprs: Vec::new(),
        ran: false,
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "callback must find the call to Wrapper::method in caller's MIR"
    );
    assert_eq!(
        callbacks.param_names,
        vec!["M"],
        "only M (own const generic) should be extracted, not N (parent)"
    );
    assert_eq!(
        callbacks.translated_exprs,
        vec![PureExpr::Int(5)],
        "M should be paired with 5 (its actual substitution), not 3 (N's value)"
    );
}

#[test]
fn closure_call_program_point_state_advances_capture_substitution() {
    let source = r#"
pub fn caller(mut x: i32) -> i32 {
    let mut c = || {
        x += 1;
        5
    };
    c();
    let after = x;
    after
}
"#;

    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["x == old(x) + 1".to_string()],
        param_names: Some(vec![]),
    };
    let (substitutions, assumptions) =
        extract_program_point_state_with_closure_user_spec(source, "caller", spec);

    assert_eq!(
        substitutions.get("x"),
        Some(&PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::Int),
        )))),
        "closure call should advance the captured source name at the program point; substitutions={substitutions:?} assumptions={assumptions:?}"
    );
}

/// Const generic method on a generic trait: `parent_count` includes Self + trait
/// const generics, so `own_params.zip(substs.skip(parent_count))` must skip all
/// parent args to reach the method's own const generic M. (#2356)
#[test]
fn const_generic_method_on_generic_trait_extracts_own_const_param() {
    let source = r#"
pub trait Parent<const N: usize> {
    fn child<const M: usize>(x: usize) -> usize;
}

pub struct Foo;

impl Parent<3> for Foo {
    #[inline(never)]
    fn child<const M: usize>(x: usize) -> usize {
        if x > 0 { M } else { 0 }
    }
}

pub fn caller(x: usize) -> usize {
    <Foo as Parent<3>>::child::<7>(x)
}
"#;

    struct TraitConstGenericCallbacks {
        param_names: Vec<String>,
        translated_exprs: Vec<PureExpr>,
        ran: bool,
    }

    impl Callbacks for TraitConstGenericCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            use rustc_middle::mir::TerminatorKind;

            for local_def_id in tcx.hir_body_owners() {
                let path = tcx.def_path_str(local_def_id);
                if !path.ends_with("::caller") && path != "caller" {
                    continue;
                }

                let body = tcx.optimized_mir(local_def_id.to_def_id());
                for bb_data in body.basic_blocks.iter() {
                    let Some(terminator) = &bb_data.terminator else {
                        continue;
                    };
                    let TerminatorKind::Call { func, .. } = &terminator.kind else {
                        continue;
                    };

                    let Operand::Constant(deref!(constant)) = func else {
                        continue;
                    };
                    let rustc_middle::ty::TyKind::FnDef(callee_def_id, _) = constant.ty().kind()
                    else {
                        continue;
                    };

                    let mut translated_args = Vec::new();
                    let mut param_names = Vec::new();
                    extend_call_with_const_generic_args(
                        tcx,
                        *callee_def_id,
                        func,
                        &mut translated_args,
                        &mut param_names,
                    );

                    self.param_names = param_names;
                    self.translated_exprs = translated_args.into_iter().map(|a| a.expr).collect();
                    self.ran = true;
                    return Compilation::Stop;
                }
            }
            Compilation::Stop
        }
    }

    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_trait_const_generic_{}_{}",
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
        "trust_wp_trait_const_generic_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = TraitConstGenericCallbacks {
        param_names: Vec::new(),
        translated_exprs: Vec::new(),
        ran: false,
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "callback must find the call to <Foo as Parent<3>>::child in caller's MIR"
    );
    assert_eq!(
        callbacks.param_names,
        vec!["M"],
        "only M (own const generic) should be extracted from trait method"
    );
    assert_eq!(
        callbacks.translated_exprs,
        vec![PureExpr::Int(7)],
        "M should be paired with 7 (its substitution), not Self/3 (parent args)"
    );
}

/// Three-level reborrow chain: `a <- b <- c`, writing `*c = 42` exercises
/// the transitive borrow chain propagation in `handle_single_deref_write`.
/// The `deref_exprs` map is correctly populated for all chain ancestors,
/// feeding into proof_assert substitution resolution. The return expression
/// path uses `local_exprs` (not `deref_exprs`), so the parameter retains
/// its reference identity. Regression test for #899.
#[test]
fn deref_assign_three_level_reborrow_chain_extracts_without_crash() {
    let source = r#"
pub fn three_level(a: &mut i32) -> i32 {
    let b = &mut *a;
    let c = &mut *b;
    *c = 42;
    *a
}
"#;

    let expr = extract_return_expr_in_source(source, "three_level")
        .expect("three-level reborrow chain should produce a return expression");
    // Return expression resolves `*a` as `Var("a", Ref(Int))` because
    // the return path uses local_exprs (parameter identity), not deref_exprs.
    // The transitive propagation populates deref_exprs for the proof_assert
    // substitution pipeline, which is the primary consumer. (#899)
    assert!(
        matches!(&expr, PureExpr::Var(name, _) if name == "a"),
        "three-level reborrow return should resolve to parameter identity, got {expr:?}"
    );
}

#[test]
fn projected_write_through_anonymous_mut_ref_call_result_preserves_deref() {
    let source = r#"
extern "Rust" {
    fn opaque_borrow(x: &mut i32) -> &mut i32;
}

pub fn write_through_result(x: &mut i32) {
    unsafe { *opaque_borrow(x) = 42; }
}
"#;

    struct ProjectedWriteLhsCallbacks {
        translated_lhs: Option<PureExpr>,
        saw_anonymous_temp: bool,
        ran: bool,
    }

    impl Callbacks for ProjectedWriteLhsCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for local_def_id in tcx.hir_body_owners() {
                let def_path = tcx.def_path_str(local_def_id);
                if def_path != "write_through_result"
                    && !def_path.ends_with("::write_through_result")
                {
                    continue;
                }

                let body = tcx.optimized_mir(local_def_id.to_def_id());
                let arg_names = resolve_arg_names_or_warn(tcx, local_def_id.to_def_id(), None);

                for bb_data in body.basic_blocks.iter() {
                    for stmt in &bb_data.statements {
                        let StatementKind::Assign((place, _)) = &stmt.kind else {
                            continue;
                        };
                        if !matches!(place.projection.as_ref(), [ProjectionElem::Deref]) {
                            continue;
                        }

                        let sort = ty_to_expr_sort_enriched(tcx, body.local_decls[place.local].ty);
                        let mut local_exprs = HashMap::new();
                        local_exprs.insert(
                            place.local,
                            PureExpr::Var("call_tmp".to_string(), sort.clone()),
                        );
                        self.saw_anonymous_temp =
                            source_name_for_local(body, place.local, &arg_names).is_none();
                        self.translated_lhs = translate_projected_write_lhs(
                            body,
                            place,
                            &local_exprs,
                            &arg_names,
                            tcx,
                        );
                        self.ran = true;
                        return Compilation::Stop;
                    }
                }
            }

            Compilation::Stop
        }
    }

    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_projected_write_lhs_{}_{}",
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
        "trust_wp_projected_write_lhs_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = ProjectedWriteLhsCallbacks {
        translated_lhs: None,
        saw_anonymous_temp: false,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to inspect anonymous mut-ref deref write"
    );
    assert!(
        callbacks.saw_anonymous_temp,
        "the deref write should target an anonymous MIR temp, not a source-named local"
    );
    assert!(
        matches!(
            callbacks.translated_lhs,
            Some(PureExpr::Deref(ref inner))
                if matches!(inner.as_ref(), PureExpr::Var(name, Some(ExprSort::MutRef(_)))
                    if name == "call_tmp")
        ),
        "anonymous mut-ref call result writes should preserve an explicit deref, got {:?}",
        callbacks.translated_lhs
    );
}

// ── ITE return expression extraction for conditional reference returns (#2687) ──

#[test]
fn if_else_returning_different_values_extracts_ite() {
    let source = r#"
pub fn pick_value(toggle: bool) -> i32 {
    if toggle { 1 } else { 2 }
}
"#;
    let expr = extract_return_expr_in_source(source, "pick_value")
        .expect("simple if-else value return should extract");
    assert!(
        expr_contains_ite(&expr),
        "if-else value return should produce ITE, got: {expr:?}"
    );
}

#[test]
fn if_else_returning_tuple_field_refs_extracts_ite() {
    let source = r#"
pub fn pair_select(p: (i32, i32), take_first: bool) -> i32 {
    if take_first { p.0 } else { p.1 }
}
"#;
    let expr = extract_return_expr_in_source(source, "pair_select")
        .expect("if-else tuple field return should extract");
    assert!(
        expr_contains_ite(&expr),
        "conditional tuple field return should produce ITE, got: {expr:?}"
    );
}

#[test]
fn if_else_returning_mut_ref_tuple_fields_extracts_ite() {
    let source = r#"
pub fn pick_mut_ref<'a>(a: &'a mut i32, b: &'a mut i32, toggle: bool) -> &'a mut i32 {
    if toggle { a } else { b }
}
"#;
    let expr = extract_return_expr_in_source(source, "pick_mut_ref")
        .expect("if-else mut ref return should extract");
    assert!(
        expr_contains_ite(&expr),
        "conditional &mut return should produce ITE, got: {expr:?}"
    );
}

#[test]
fn if_else_returning_tuple_mut_ref_pair_extracts_ite() {
    let source = r#"
pub fn pair_bor_mut<'a, T>(p: (&'a mut T, &'a mut T), take_first: bool) -> &'a mut T {
    if take_first { p.0 } else { p.1 }
}
"#;
    let expr = extract_return_expr_in_source(source, "pair_bor_mut");
    assert!(
        expr.is_some(),
        "pair_bor_mut should extract a return expression"
    );
    let expr = expr.unwrap();
    assert!(
        expr_contains_ite(&expr),
        "pair_bor_mut should produce ITE for conditional tuple field return, got: {expr:?}"
    );
}

#[test]
fn projected_mut_ref_return_to_tuple_field_extracts() {
    let source = r#"
pub fn reborrow_field<T>(r: &mut (T, T)) -> &mut T {
    &mut r.0
}
"#;
    let expr = extract_return_expr_in_source(source, "reborrow_field")
        .expect("projected &mut field return should extract");

    assert!(
        matches!(
            &expr,
            PureExpr::LogicFnCall { name, args }
                if name == &tuple_field_logic_fn_name(0)
                    && matches!(args.as_slice(), [PureExpr::Var(arg, _)] if arg == "r")
        ),
        "reborrow_field should return tuple_get_0(r), got: {expr:?}"
    );
}

#[test]
fn tuple_of_projected_mut_ref_field_returns_extracts() {
    let source = r#"
pub fn disjoint_fields<T>(r: &mut (T, T)) -> (&mut T, &mut T) {
    let r0 = &mut r.0;
    let r1 = &mut r.1;
    (r0, r1)
}
"#;
    let expr = extract_return_expr_in_source(source, "disjoint_fields")
        .expect("tuple of projected &mut field returns should extract");

    let PureExpr::LogicFnCall { name, args } = &expr else {
        panic!("disjoint_fields should return a tuple constructor, got: {expr:?}");
    };
    assert_eq!(name, &tuple_logic_fn_name(2));
    assert!(
        matches!(
            args.as_slice(),
            [
                PureExpr::LogicFnCall { name: left_name, args: left_args },
                PureExpr::LogicFnCall { name: right_name, args: right_args },
            ] if left_name == &tuple_field_logic_fn_name(0)
                && right_name == &tuple_field_logic_fn_name(1)
                && matches!(left_args.as_slice(), [PureExpr::Var(arg, _)] if arg == "r")
                && matches!(right_args.as_slice(), [PureExpr::Var(arg, _)] if arg == "r")
        ),
        "disjoint_fields should return both projected field refs, got: {expr:?}"
    );
}

#[test]
fn nested_projected_mut_ref_field_return_extracts() {
    let source = r#"
pub fn nested_fields<T>(r: &mut ((T, T), T)) -> &mut T {
    let borrow1 = &mut r.0;
    &mut borrow1.1
}
"#;
    let expr = extract_return_expr_in_source(source, "nested_fields")
        .expect("nested projected &mut field return should extract");

    assert!(
        matches!(
            &expr,
            PureExpr::LogicFnCall { name, args }
                if name == &tuple_field_logic_fn_name(1)
                    && matches!(
                        args.as_slice(),
                        [PureExpr::LogicFnCall { name: inner_name, args: inner_args }]
                            if inner_name == &tuple_field_logic_fn_name(0)
                                && matches!(
                                    inner_args.as_slice(),
                                    [PureExpr::Var(arg, _)] if arg == "r"
                                )
                    )
        ),
        "nested_fields should return tuple_get_1(tuple_get_0(r)), got: {expr:?}"
    );
}

#[test]
fn match_expr_returning_mut_refs_extracts_ite() {
    let source = r#"
pub fn match_select<'a>(a: &'a mut i32, b: &'a mut i32, c: &'a mut i32, n: i32) -> &'a mut i32 {
    match n {
        0 => a,
        1 => b,
        _ => c,
    }
}
"#;
    let expr = extract_return_expr_in_source(source, "match_select");
    assert!(expr.is_some(), "match returning &mut refs should extract");
    let expr = expr.unwrap();
    assert!(
        expr_contains_ite(&expr),
        "match returning different &mut refs should produce ITE chain, got: {expr:?}"
    );
}
