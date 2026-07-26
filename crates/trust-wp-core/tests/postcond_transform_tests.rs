// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for postcondition transformation methods on `PureExpr`.
//!
//! Coverage gap: `postcond.rs` (814 LOC) has zero `#[cfg(test)]` blocks.
//! Three pub methods:
//! - `transform_postcondition_for_mut_refs`: Deref(Var(x)) → Final(Var(x))
//!   for mut ref params (outside Old)
//! - `transform_closure_capture_postcondition`: Var(self.N) → Final(Deref(Var(self.N)))
//!   outside Old, → Deref inside Old
//! - `transform_closure_capture_precondition`: Var(self.N) → Deref(Var(self.N))

use std::{collections::HashSet, sync::Arc};

use trust_wp_core::formula::{BinOp, PureExpr};

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn int(v: i64) -> PureExpr {
    PureExpr::Int(v)
}

fn deref(e: PureExpr) -> PureExpr {
    PureExpr::Deref(Arc::new(e))
}

fn final_expr(e: PureExpr) -> PureExpr {
    PureExpr::Final(Arc::new(e))
}

fn old(e: PureExpr) -> PureExpr {
    PureExpr::Old(Arc::new(e))
}

fn mut_refs(names: &[&str]) -> HashSet<String> {
    names.iter().copied().map(String::from).collect()
}

fn captures(names: &[&str]) -> HashSet<String> {
    names.iter().copied().map(String::from).collect()
}

// === transform_postcondition_for_mut_refs ===

#[test]
fn mut_ref_deref_becomes_final() {
    // *x → ^x for mut ref param
    let expr = deref(var("x"));
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    assert_eq!(result, final_expr(var("x")));
}

#[test]
fn mut_ref_old_deref_stays() {
    // old(*x) stays as old(*x)
    let expr = old(deref(var("x")));
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    assert_eq!(result, old(deref(var("x"))));
}

#[test]
fn mut_ref_non_param_deref_unchanged() {
    // *y where y is NOT a mut ref param — stays as *y
    let expr = deref(var("y"));
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    assert_eq!(result, deref(var("y")));
}

#[test]
fn mut_ref_literal_unchanged() {
    let expr = int(42);
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    assert_eq!(result, int(42));
}

#[test]
fn mut_ref_in_binop() {
    // *x == old(*x) + 1
    let expr = PureExpr::BinOp(
        Arc::new(deref(var("x"))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(old(deref(var("x")))),
            BinOp::Add,
            Arc::new(int(1)),
        )),
    );
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    // ^x == old(*x) + 1
    let expected = PureExpr::BinOp(
        Arc::new(final_expr(var("x"))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(old(deref(var("x")))),
            BinOp::Add,
            Arc::new(int(1)),
        )),
    );
    assert_eq!(result, expected);
}

#[test]
fn mut_ref_empty_params_no_change() {
    let expr = deref(var("x"));
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&[]));
    assert_eq!(result, deref(var("x")));
}

#[test]
fn mut_ref_multiple_params() {
    // *x + *y where both are mut ref params
    let expr = PureExpr::BinOp(
        Arc::new(deref(var("x"))),
        BinOp::Add,
        Arc::new(deref(var("y"))),
    );
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x", "y"]));
    let expected = PureExpr::BinOp(
        Arc::new(final_expr(var("x"))),
        BinOp::Add,
        Arc::new(final_expr(var("y"))),
    );
    assert_eq!(result, expected);
}

#[test]
fn mut_ref_bare_var_becomes_deref() {
    // x (bare Var for mut ref param) → Deref(x) so it maps to x_current (#609)
    let expr = var("x");
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    assert_eq!(result, deref(var("x")));
}

#[test]
fn mut_ref_nested_deref_view() {
    // View(*x) where x is mut ref → View(^x)
    let expr = PureExpr::View(Arc::new(deref(var("x"))));
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    assert_eq!(result, PureExpr::View(Arc::new(final_expr(var("x")))));
}

// === transform_closure_capture_postcondition ===

#[test]
fn closure_capture_var_becomes_final() {
    // self.0 → Final(Deref(self.0)) in postcondition (outside old)
    let expr = var("self.0");
    let result = expr.transform_closure_capture_postcondition(&captures(&["self.0"]));
    assert_eq!(result, final_expr(deref(var("self.0"))));
}

#[test]
fn closure_capture_var_in_old_becomes_deref() {
    // old(self.0) → old(Deref(self.0))
    let expr = old(var("self.0"));
    let result = expr.transform_closure_capture_postcondition(&captures(&["self.0"]));
    assert_eq!(result, old(deref(var("self.0"))));
}

#[test]
fn closure_capture_deref_var_in_old_stays_single_deref() {
    let expr = old(deref(var("self.0")));
    let result = expr.transform_closure_capture_postcondition(&captures(&["self.0"]));
    assert_eq!(result, old(deref(var("self.0"))));
}

#[test]
fn closure_capture_non_capture_unchanged() {
    let expr = var("other");
    let result = expr.transform_closure_capture_postcondition(&captures(&["self.0"]));
    assert_eq!(result, var("other"));
}

#[test]
fn closure_capture_literal_unchanged() {
    let expr = int(42);
    let result = expr.transform_closure_capture_postcondition(&captures(&["self.0"]));
    assert_eq!(result, int(42));
}

#[test]
fn closure_capture_in_binop() {
    // self.0 == old(self.0) + 1
    let expr = PureExpr::BinOp(
        Arc::new(var("self.0")),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(old(var("self.0"))),
            BinOp::Add,
            Arc::new(int(1)),
        )),
    );
    let result = expr.transform_closure_capture_postcondition(&captures(&["self.0"]));
    // Final(Deref(self.0)) == old(Deref(self.0)) + 1
    let expected = PureExpr::BinOp(
        Arc::new(final_expr(deref(var("self.0")))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(old(deref(var("self.0")))),
            BinOp::Add,
            Arc::new(int(1)),
        )),
    );
    assert_eq!(result, expected);
}

#[test]
fn closure_capture_multiple_fields() {
    let expr = PureExpr::BinOp(Arc::new(var("self.0")), BinOp::Add, Arc::new(var("self.1")));
    let result = expr.transform_closure_capture_postcondition(&captures(&["self.0", "self.1"]));
    let expected = PureExpr::BinOp(
        Arc::new(final_expr(deref(var("self.0")))),
        BinOp::Add,
        Arc::new(final_expr(deref(var("self.1")))),
    );
    assert_eq!(result, expected);
}

#[test]
fn closure_capture_view_becomes_view_of_final_deref() {
    let expr = PureExpr::View(Arc::new(var("self.0")));
    let result = expr.transform_closure_capture_postcondition(&captures(&["self.0"]));
    let expected = PureExpr::View(Arc::new(final_expr(deref(var("self.0")))));
    assert_eq!(result, expected);
}

#[test]
fn closure_capture_view_of_deref_becomes_view_of_final_deref() {
    let expr = PureExpr::View(Arc::new(deref(var("self.0"))));
    let result = expr.transform_closure_capture_postcondition(&captures(&["self.0"]));
    let expected = PureExpr::View(Arc::new(final_expr(deref(var("self.0")))));
    assert_eq!(result, expected);
}

// === transform_closure_capture_precondition ===

#[test]
fn closure_precondition_var_becomes_deref() {
    // self.0 → Deref(self.0) in precondition
    let expr = var("self.0");
    let result = expr.transform_closure_capture_precondition(&captures(&["self.0"]));
    assert_eq!(result, deref(var("self.0")));
}

#[test]
fn closure_precondition_deref_var_stays_single_deref() {
    let expr = deref(var("self.0"));
    let result = expr.transform_closure_capture_precondition(&captures(&["self.0"]));
    assert_eq!(result, deref(var("self.0")));
}

#[test]
fn closure_precondition_non_capture_unchanged() {
    let expr = var("other");
    let result = expr.transform_closure_capture_precondition(&captures(&["self.0"]));
    assert_eq!(result, var("other"));
}

#[test]
fn closure_precondition_in_binop() {
    let expr = PureExpr::BinOp(Arc::new(var("self.0")), BinOp::Gt, Arc::new(int(0)));
    let result = expr.transform_closure_capture_precondition(&captures(&["self.0"]));
    let expected = PureExpr::BinOp(Arc::new(deref(var("self.0"))), BinOp::Gt, Arc::new(int(0)));
    assert_eq!(result, expected);
}

#[test]
fn closure_precondition_empty_captures_no_change() {
    let expr = var("self.0");
    let result = expr.transform_closure_capture_precondition(&captures(&[]));
    assert_eq!(result, var("self.0"));
}

#[test]
fn closure_precondition_method_call() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(var("self.0")),
        method: "len".to_string(),
        args: vec![],
    };
    let result = expr.transform_closure_capture_precondition(&captures(&["self.0"]));
    let expected = PureExpr::MethodCall {
        receiver: Arc::new(deref(var("self.0"))),
        method: "len".to_string(),
        args: vec![],
    };
    assert_eq!(result, expected);
}

// === Explicit final vars: ^x alongside *x (#609) ===

#[test]
fn mut_ref_explicit_final_preserves_deref_as_current() {
    // When postcondition uses both ^x and *x, *x should stay as Deref(current)
    // instead of being rewritten to Final.
    // Expr: ^x == *x + 1
    let expr = PureExpr::BinOp(
        Arc::new(final_expr(var("x"))),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(deref(var("x"))),
            BinOp::Add,
            Arc::new(int(1)),
        )),
    );
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    assert_eq!(result, expr, "explicit ^x should prevent *x → ^x rewrite");
}

#[test]
fn mut_ref_explicit_final_inside_old_not_detected() {
    // old(^x) should NOT mark x as explicit-final — ^x inside old() doesn't
    // indicate user intent for the outer scope.
    let expr = PureExpr::BinOp(
        Arc::new(deref(var("x"))),
        BinOp::Eq,
        Arc::new(old(final_expr(var("x")))),
    );
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    let expected = PureExpr::BinOp(
        Arc::new(final_expr(var("x"))),
        BinOp::Eq,
        Arc::new(old(final_expr(var("x")))),
    );
    assert_eq!(result, expected);
}

// === Ite (if-then-else) ===

#[test]
fn mut_ref_ite_transforms_all_branches() {
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(deref(var("x"))),
        Arc::new(deref(var("y"))),
    );
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x", "y"]));
    let expected = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(final_expr(var("x"))),
        Arc::new(final_expr(var("y"))),
    );
    assert_eq!(result, expected);
}

#[test]
fn closure_capture_ite() {
    let expr = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(var("self.0")),
        Arc::new(int(0)),
    );
    let result = expr.transform_closure_capture_postcondition(&captures(&["self.0"]));
    let expected = PureExpr::Ite(
        Arc::new(PureExpr::Bool(true)),
        Arc::new(final_expr(deref(var("self.0")))),
        Arc::new(int(0)),
    );
    assert_eq!(result, expected);
}

// === Forall / Exists ===

#[test]
fn mut_ref_forall_transforms_body() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(deref(var("x"))),
            BinOp::Gt,
            Arc::new(var("i")),
        )),
        triggers: vec![],
    };
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    match result {
        PureExpr::Forall { body, .. } => {
            let expected_body = PureExpr::BinOp(
                Arc::new(final_expr(var("x"))),
                BinOp::Gt,
                Arc::new(var("i")),
            );
            assert_eq!(*body, expected_body);
        }
        other => panic!("expected Forall, got {other:?}"),
    }
}

#[test]
fn mut_ref_exists_transforms_body() {
    let expr = PureExpr::Exists {
        var: "i".to_string(),
        var_sort: None,
        body: Arc::new(PureExpr::BinOp(
            Arc::new(deref(var("x"))),
            BinOp::Eq,
            Arc::new(var("i")),
        )),
        triggers: vec![],
    };
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    match result {
        PureExpr::Exists { body, .. } => {
            let expected_body = PureExpr::BinOp(
                Arc::new(final_expr(var("x"))),
                BinOp::Eq,
                Arc::new(var("i")),
            );
            assert_eq!(*body, expected_body);
        }
        other => panic!("expected Exists, got {other:?}"),
    }
}

// === LogicFnCall ===

#[test]
fn mut_ref_logic_fn_call_transforms_args() {
    let expr = PureExpr::LogicFnCall {
        name: "my_logic_fn".to_string(),
        args: vec![deref(var("x")), int(5)],
    };
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    let expected = PureExpr::LogicFnCall {
        name: "my_logic_fn".to_string(),
        args: vec![final_expr(var("x")), int(5)],
    };
    assert_eq!(result, expected);
}

#[test]
fn closure_capture_logic_fn_call() {
    let expr = PureExpr::LogicFnCall {
        name: "pred".to_string(),
        args: vec![var("self.0")],
    };
    let result = expr.transform_closure_capture_postcondition(&captures(&["self.0"]));
    let expected = PureExpr::LogicFnCall {
        name: "pred".to_string(),
        args: vec![final_expr(deref(var("self.0")))],
    };
    assert_eq!(result, expected);
}

// === Match ===

#[test]
fn mut_ref_match_transforms_scrutinee_and_arms() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let expr = PureExpr::Match {
        scrutinee: Arc::new(deref(var("x"))),
        arms: vec![
            MatchArm {
                pattern: Pattern::Literal(PureExpr::Int(0)),
                body: deref(var("x")),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: int(99),
            },
        ],
    };
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    match result {
        PureExpr::Match { scrutinee, arms } => {
            assert_eq!(*scrutinee, final_expr(var("x")));
            assert_eq!(arms[0].body, final_expr(var("x")));
            assert_eq!(arms[1].body, int(99));
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

// === Let binding ===

#[test]
fn mut_ref_let_transforms_value_and_body() {
    let expr = PureExpr::Let {
        var: "tmp".to_string(),
        value: Arc::new(deref(var("x"))),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("tmp")),
            BinOp::Add,
            Arc::new(int(1)),
        )),
    };
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    match result {
        PureExpr::Let { value, .. } => {
            assert_eq!(*value, final_expr(var("x")));
        }
        other => panic!("expected Let, got {other:?}"),
    }
}

// === UnOp ===

#[test]
fn mut_ref_unop_transforms_operand() {
    use trust_wp_core::formula::UnOp;
    let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(deref(var("x"))));
    let result = expr.transform_postcondition_for_mut_refs(&mut_refs(&["x"]));
    assert_eq!(
        result,
        PureExpr::UnOp(UnOp::Neg, Arc::new(final_expr(var("x"))))
    );
}
