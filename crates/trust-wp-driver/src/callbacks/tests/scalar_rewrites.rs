// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    shared::{collect_structural_proof_assert_rewrite, find_arm},
    *,
};

// --- collapse_idempotent_views: is_provably_view_identity_domain branches ---

#[test]
fn test_collapse_view_of_int_literal() {
    let input = PureExpr::View(Arc::new(PureExpr::Int(42)));
    let result = collapse_idempotent_views(input);
    assert_eq!(
        result,
        PureExpr::Int(42),
        "View(Int) → Int (identity domain)"
    );
}

#[test]
fn test_collapse_view_of_bool_literal() {
    let input = PureExpr::View(Arc::new(PureExpr::Bool(true)));
    let result = collapse_idempotent_views(input);
    assert_eq!(
        result,
        PureExpr::Bool(true),
        "View(Bool) → Bool (identity domain)"
    );
}

#[test]
#[allow(clippy::approx_constant)] // intentional: testing float encoding, not using PI
fn test_collapse_view_of_float_literal() {
    let input = PureExpr::View(Arc::new(PureExpr::Float(
        trust_wp_core::formula::FloatBits::from_f64(3.14),
    )));
    let result = collapse_idempotent_views(input.clone());
    match result {
        PureExpr::Float(_) => {} // collapsed
        other => panic!("expected Float, got {other:?}"),
    }
}

#[test]
fn test_collapse_view_of_ite_all_scalar() {
    // View(ite(true, 1, 2)) → ite(true, 1, 2) because all branches are scalar
    let ite = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(PureExpr::Int(1)),
        Arc::new(PureExpr::Int(2)),
    );
    let input = PureExpr::View(Arc::new(ite.clone()));
    let result = collapse_idempotent_views(input);
    assert_eq!(result, ite, "View(Ite(scalar, scalar, scalar)) → Ite");
}

#[test]
fn test_collapse_view_of_ite_non_scalar_branch_preserved() {
    // View(ite(true, 1, Var("x", None))) — branch Var(x, None) is not provably
    // scalar, so View is preserved.
    let ite = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(PureExpr::Int(1)),
        Arc::new(PureExpr::Var("x".to_string(), None)),
    );
    let input = PureExpr::View(Arc::new(ite));
    let result = collapse_idempotent_views(input.clone());
    assert_eq!(result, input, "View(Ite with non-scalar branch) preserved");
}

#[test]
fn test_collapse_view_of_old_scalar() {
    // View(Old(Int(5))) → Old(Int(5))
    let inner = PureExpr::Old(Arc::new(PureExpr::Int(5)));
    let input = PureExpr::View(Arc::new(inner.clone()));
    let result = collapse_idempotent_views(input);
    assert_eq!(result, inner, "View(Old(scalar)) → Old(scalar)");
}

#[test]
fn test_collapse_view_of_deref_non_scalar_preserved() {
    // View(Deref(Var("x", None))) — Var's sort is None, so not provably scalar.
    let inner = PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None)));
    let input = PureExpr::View(Arc::new(inner));
    let result = collapse_idempotent_views(input.clone());
    assert_eq!(
        result, input,
        "View(Deref(Var(x, None))) preserved — unknown sort"
    );
}

#[test]
fn test_collapse_view_of_let_scalar_body() {
    // View(let x = 1 in 2) → let x = 1 in 2
    let let_expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(PureExpr::Int(1)),
        body: Arc::new(PureExpr::Int(2)),
    };
    let input = PureExpr::View(Arc::new(let_expr.clone()));
    let result = collapse_idempotent_views(input);
    assert_eq!(result, let_expr, "View(Let(scalar body)) → Let");
}

#[test]
fn test_collapse_view_of_match_all_scalar_arms() {
    let match_expr = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("x".to_string(), None)),
        arms: vec![
            MatchArm {
                pattern: Pattern::Literal(PureExpr::Int(0)),
                body: PureExpr::Int(10),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Int(20),
            },
        ],
    };
    let input = PureExpr::View(Arc::new(match_expr.clone()));
    let result = collapse_idempotent_views(input);
    assert_eq!(result, match_expr, "View(Match(all scalar arms)) → Match");
}

#[test]
fn test_collapse_view_of_datatype_var_preserved() {
    // View(Var("x", Datatype)) should NOT collapse — Datatype is not scalar identity
    let input = PureExpr::View(Arc::new(PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::Datatype(
            trust_wp_core::formula::intern_sort_name("MyStruct"),
        )),
    )));
    let result = collapse_idempotent_views(input.clone());
    assert_eq!(
        result, input,
        "View(Var(x, Datatype)) preserved — not scalar identity"
    );
}

// --- normalize_scalar_proof_assert_boundary tests ---

/// Empty inputs — no changes, no panics.
#[test]
fn test_normalize_scalar_boundary_empty() {
    let mut pre: Vec<PureExpr> = vec![];
    let mut ens: Vec<PureExpr> = vec![];
    let mut ret: Option<PureExpr> = None;
    normalize_scalar_proof_assert_boundary(&mut pre, &mut ens, &mut ret);
    assert!(pre.is_empty());
    assert!(ens.is_empty());
    assert!(ret.is_none());
}

/// No scalar `Deref(Var)` patterns — expressions pass through unchanged.
#[test]
fn test_normalize_scalar_boundary_no_scalar_patterns() {
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let mut pre = vec![expr.clone()];
    let mut ens: Vec<PureExpr> = vec![];
    let mut ret: Option<PureExpr> = None;
    normalize_scalar_proof_assert_boundary(&mut pre, &mut ens, &mut ret);
    assert_eq!(pre[0], expr, "no scalar patterns → unchanged");
}

/// `Deref(Var("x")) == Int(5)` in ensures triggers materialization:
/// `Deref(Var("x"))` → `Var("x_current", Int)` in both preconditions and ensures.
#[test]
fn test_normalize_scalar_boundary_deref_var_eq_int() {
    // ensures: *x == 5
    let deref_x = PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None)));
    let ensure = PureExpr::BinOp(
        Arc::new(deref_x.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    );
    // preconditions also reference *x
    let precond = PureExpr::BinOp(Arc::new(deref_x), BinOp::Gt, Arc::new(PureExpr::Int(0)));

    let mut pre = vec![precond];
    let mut ens = vec![ensure];
    let mut ret: Option<PureExpr> = None;
    normalize_scalar_proof_assert_boundary(&mut pre, &mut ens, &mut ret);

    // The ensures should have *x → x_current
    let expected_ens = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x_current".to_string(), Some(ExprSort::Int))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(5)),
    );
    assert_eq!(ens[0], expected_ens, "ensures: *x should become x_current");

    // The preconditions should also have *x → x_current
    let expected_pre = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x_current".to_string(), Some(ExprSort::Int))),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    assert_eq!(
        pre[0], expected_pre,
        "preconditions: *x should become x_current"
    );
}

/// return_expr also gets materialized.
#[test]
fn test_normalize_scalar_boundary_return_expr_materialized() {
    let deref_x = PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None)));
    let ensure = PureExpr::BinOp(
        Arc::new(deref_x.clone()),
        BinOp::Eq,
        Arc::new(PureExpr::Int(10)),
    );
    let ret_expr = deref_x;

    let mut pre: Vec<PureExpr> = vec![];
    let mut ens = vec![ensure];
    let mut ret = Some(ret_expr);
    normalize_scalar_proof_assert_boundary(&mut pre, &mut ens, &mut ret);

    let expected_ret = PureExpr::Var("x_current".to_string(), Some(ExprSort::Int));
    assert_eq!(
        ret,
        Some(expected_ret),
        "return_expr: *x should become x_current"
    );
}

/// View(Var("y", Int)) materializes to Var("y", Int) when sort is scalar.
#[test]
fn test_normalize_scalar_boundary_view_of_annotated_scalar() {
    // Create an equality that triggers sort collection:
    // *z == Bool(true)  → z is scalar
    let deref_z = PureExpr::Deref(Arc::new(PureExpr::Var("z".to_string(), None)));
    let ensure = PureExpr::BinOp(Arc::new(deref_z), BinOp::Eq, Arc::new(PureExpr::Bool(true)));
    // The precondition has View(Var("y", Int)) — scalar view identity
    let view_y = PureExpr::View(Arc::new(PureExpr::Var(
        "y".to_string(),
        Some(ExprSort::Int),
    )));
    let precond = PureExpr::BinOp(Arc::new(view_y), BinOp::Gt, Arc::new(PureExpr::Int(0)));

    let mut pre = vec![precond];
    let mut ens = vec![ensure];
    let mut ret: Option<PureExpr> = None;
    normalize_scalar_proof_assert_boundary(&mut pre, &mut ens, &mut ret);

    // View(Var("y", Int)) → Var("y", Int) because scalar view is identity
    let expected_pre = PureExpr::BinOp(
        Arc::new(PureExpr::Var("y".to_string(), Some(ExprSort::Int))),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    assert_eq!(
        pre[0], expected_pre,
        "View(Var(y, Int)) should materialize to Var(y, Int)"
    );
}

#[test]
fn test_apply_type_and_field_rewrites_expands_structural_inv_calls() {
    let source = r#"
#![allow(dead_code)]

pub struct NonZero(i32);

pub fn use_option(x: Option<NonZero>) {
let _ = x;
}
"#;

    let (assertion, preconditions) = collect_structural_proof_assert_rewrite(source);

    assert_eq!(
        preconditions,
        vec![assertion.clone()],
        "proof_assert preconditions should share the same structural rewrite as the assertion"
    );

    let PureExpr::Match { scrutinee, arms } = assertion else {
        panic!("expected structural match rewrite, got {assertion:?}");
    };
    assert!(
        matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "x"),
        "structural rewrite should match on the proof_assert parameter, got {scrutinee:?}"
    );
    assert_eq!(arms.len(), 2, "Option should produce Some/None arms");
    assert!(
        matches!(
            &find_arm(&arms, "Some").body,
            PureExpr::MethodCall { method, .. } if method.contains("NonZero")
        ),
        "Some arm should call the NonZero invariant: {:?}",
        find_arm(&arms, "Some").body
    );
    assert!(
        matches!(find_arm(&arms, "None").body, PureExpr::Bool(true)),
        "None arm should stay trivial: {:?}",
        find_arm(&arms, "None").body
    );
}
