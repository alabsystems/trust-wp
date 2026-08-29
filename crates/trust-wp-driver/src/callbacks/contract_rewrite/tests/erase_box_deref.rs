// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Box deref erasure in contract expressions (#3323).
//!
//! Box<T> is transparent: `ty_to_expr_sort_enriched` peels Box and assigns the
//! inner type's sort. The contract parser produces `Deref(Var("x"))` for `*x`,
//! but since the sort already reflects the inner type, the extra Deref layer is
//! spurious. `erase_box_deref_expr` removes it so the encoder doesn't
//! misinterpret it as a MutRef deref.

use super::*;

#[test]
fn test_erase_box_deref_simple_var() {
    // Deref(Var("x")) -> Var("x") when x is a Box param
    let box_params = HashSet::from(["x".to_string()]);
    let expr = PureExpr::Deref(Arc::new(PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    )));

    let result = erase_box_deref_expr(&expr, &box_params);

    assert_eq!(
        result,
        PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
        )
    );
}

#[test]
fn test_erase_box_deref_non_box_param_preserved() {
    // Deref(Var("y")) is NOT erased when y is not a Box param
    let box_params = HashSet::from(["x".to_string()]);
    let expr = PureExpr::Deref(Arc::new(PureExpr::Var(
        "y".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    )));

    let result = erase_box_deref_expr(&expr, &box_params);

    // Unchanged — y is not a Box param
    assert_eq!(result, expr);
}

#[test]
fn test_erase_box_deref_double_deref() {
    // Deref(Deref(Var("x"))) -> Deref(Var("x"))
    // Outer Box deref erased, inner MutRef deref preserved
    let box_params = HashSet::from(["x".to_string()]);
    let var_x = PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    );
    let expr = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(var_x.clone()))));

    let result = erase_box_deref_expr(&expr, &box_params);

    // Inner Deref(Var("x")) had its Box deref erased -> Var("x")
    // Outer Deref wraps the result -> Deref(Var("x"))
    assert_eq!(result, PureExpr::Deref(Arc::new(var_x)));
}

#[test]
fn test_erase_box_final_simple_var() {
    // Final(Var("x")) -> Var("x") when x is a Box param
    let box_params = HashSet::from(["x".to_string()]);
    let expr = PureExpr::Final(Arc::new(PureExpr::Var(
        "x".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    )));

    let result = erase_box_deref_expr(&expr, &box_params);

    assert_eq!(
        result,
        PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
        )
    );
}

#[test]
fn test_erase_box_deref_in_binop() {
    // result == Deref(Var("x")) -> result == Var("x")
    let box_params = HashSet::from(["x".to_string()]);
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )))),
    );

    let result = erase_box_deref_expr(&expr, &box_params);

    assert_eq!(
        result,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var(
                "x".to_string(),
                Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
            )),
        )
    );
}

#[test]
fn test_erase_box_deref_empty_set() {
    // No box params -> nothing erased
    let box_params = HashSet::new();
    let expr = PureExpr::Deref(Arc::new(PureExpr::Var("x".to_string(), None)));

    let result = erase_box_deref_expr(&expr, &box_params);

    assert_eq!(result, expr);
}

// --- Closure capture tests (#2668) ---
// After closure_capture_substitutions runs, capture names like "bx" become
// "self.0", "self.1", etc. The Box deref erasure must recognize these
// substituted names too.

#[test]
fn test_erase_box_deref_closure_self_field_name() {
    // Deref(Var("self.1")) -> Var("self.1") when self.1 is a Box capture
    let box_params = HashSet::from(["bx".to_string(), "self.1".to_string()]);
    let expr = PureExpr::Deref(Arc::new(PureExpr::Var(
        "self.1".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    )));

    let result = erase_box_deref_expr(&expr, &box_params);

    assert_eq!(
        result,
        PureExpr::Var(
            "self.1".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
        )
    );
}

#[test]
fn test_erase_box_deref_closure_multiple_captures() {
    // Two Box captures: self.0 and self.1 both get deref erasure
    let box_params = HashSet::from(["self.0".to_string(), "self.1".to_string()]);

    // Expression: Deref(Var("self.0")) + Deref(Var("self.1"))
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "self.0".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )))),
        BinOp::Add,
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "self.1".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )))),
    );

    let result = erase_box_deref_expr(&expr, &box_params);

    assert_eq!(
        result,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var(
                "self.0".to_string(),
                Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
            )),
            BinOp::Add,
            Arc::new(PureExpr::Var(
                "self.1".to_string(),
                Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
            )),
        )
    );
}

#[test]
fn test_erase_box_deref_closure_non_box_capture_preserved() {
    // self.0 is a Box capture, self.2 is not — only self.0 gets erasure
    let box_params = HashSet::from(["self.0".to_string()]);

    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "self.0".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "self.2".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
        )))),
    );

    let result = erase_box_deref_expr(&expr, &box_params);

    // self.0 deref erased, self.2 deref preserved
    assert_eq!(
        result,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var(
                "self.0".to_string(),
                Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
            )),
            BinOp::Eq,
            Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
                "self.2".to_string(),
                Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
            )))),
        )
    );
}

#[test]
fn test_erase_box_deref_closure_old_wrapped() {
    // Old(Deref(Var("self.1"))) -> Old(Var("self.1")) when self.1 is Box capture
    // This pattern appears in closure contracts like `old(*bx)` which becomes
    // `Old(Deref(Var("self.1")))` after capture substitution.
    let box_params = HashSet::from(["self.1".to_string()]);
    let expr = PureExpr::Old(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
        "self.1".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    )))));

    let result = erase_box_deref_expr(&expr, &box_params);

    assert_eq!(
        result,
        PureExpr::Old(Arc::new(PureExpr::Var(
            "self.1".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
        )))
    );
}

#[test]
fn test_erase_box_final_closure_capture() {
    // Final(Var("self.0")) -> Var("self.0") when self.0 is Box capture
    // The ^(box_val) pattern for Box's final state.
    let box_params = HashSet::from(["self.0".to_string()]);
    let expr = PureExpr::Final(Arc::new(PureExpr::Var(
        "self.0".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    )));

    let result = erase_box_deref_expr(&expr, &box_params);

    assert_eq!(
        result,
        PureExpr::Var(
            "self.0".to_string(),
            Some(ExprSort::MutRef(Box::new(ExprSort::Int)))
        )
    );
}

#[test]
fn test_erase_box_deref_closure_double_deref_box_mut_ref() {
    // Deref(Deref(Var("self.1"))) -> Deref(Var("self.1"))
    // Box<&mut i32> captured: outer deref is spurious Box, inner is MutRef deref
    let box_params = HashSet::from(["self.1".to_string()]);
    let var = PureExpr::Var(
        "self.1".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    );
    let expr = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(var.clone()))));

    let result = erase_box_deref_expr(&expr, &box_params);

    // Inner Deref(Var("self.1")) -> Var("self.1") (Box deref erased)
    // Outer Deref wraps result -> Deref(Var("self.1")) (MutRef deref preserved)
    assert_eq!(result, PureExpr::Deref(Arc::new(var)));
}

// --- Deref-of-Old-of-Var pattern tests (#2668) ---
// Contract expressions like `*old(bx)` parse as `Deref(Old(Var("bx")))`.
// After capture substitution: `Deref(Old(Var("self.1")))`. The Box deref
// erasure must handle wrappers between Deref and Var.

#[test]
fn test_erase_box_deref_old_wrapped_var() {
    // Deref(Old(Var("self.1"))) -> Old(Var("self.1")) for Box<&mut i32>
    // Pattern: `*old(bx)` where bx: Box<&mut i32>
    let box_params = HashSet::from(["self.1".to_string()]);
    let var = PureExpr::Var(
        "self.1".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    );
    let expr = PureExpr::Deref(Arc::new(PureExpr::Old(Arc::new(var.clone()))));

    let result = erase_box_deref_expr(&expr, &box_params);

    // Box deref erased: Deref(Old(Var("self.1"))) -> Old(Var("self.1"))
    assert_eq!(result, PureExpr::Old(Arc::new(var)));
}

#[test]
fn test_erase_box_deref_double_deref_old_box_box_mut_ref() {
    // Deref(Deref(Old(Var("self.2")))) -> Old(Var("self.2"))
    // Pattern: `**old(by)` where by: Box<Box<&mut i32>> (two Box layers)
    let box_params = HashSet::from(["self.2".to_string()]);
    let var = PureExpr::Var(
        "self.2".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    );
    let expr = PureExpr::Deref(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Old(
        Arc::new(var.clone()),
    )))));

    let result = erase_box_deref_expr(&expr, &box_params);

    // Both Box deref layers erased: Deref(Deref(Old(Var("self.2")))) -> Old(Var("self.2"))
    assert_eq!(result, PureExpr::Old(Arc::new(var)));
}

#[test]
fn test_erase_box_deref_full_fnonce_postcondition_pattern() {
    // Full postcondition pattern from 09_fnonce_resolve:
    // View(Final(Deref(Old(Var("self.1"))))) -> View(Final(Old(Var("self.1"))))
    // Represents: (^*old(bx))@ where bx: Box<&mut i32>
    let box_params = HashSet::from(["self.1".to_string()]);
    let var = PureExpr::Var(
        "self.1".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    );
    let expr = PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Deref(
        Arc::new(PureExpr::Old(Arc::new(var.clone()))),
    )))));

    let result = erase_box_deref_expr(&expr, &box_params);

    // Box deref erased inside Final: View(Final(Old(Var("self.1"))))
    assert_eq!(
        result,
        PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Old(
            Arc::new(var)
        )))))
    );
}

#[test]
fn test_erase_box_deref_full_double_box_postcondition_pattern() {
    // Full postcondition pattern for Box<Box<&mut i32>>:
    // View(Final(Deref(Deref(Old(Var("self.2")))))) -> View(Final(Old(Var("self.2"))))
    // Represents: (^**old(by))@ where by: Box<Box<&mut i32>>
    let box_params = HashSet::from(["self.2".to_string()]);
    let var = PureExpr::Var(
        "self.2".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    );
    let expr = PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Deref(
        Arc::new(PureExpr::Deref(Arc::new(PureExpr::Old(Arc::new(
            var.clone(),
        ))))),
    )))));

    let result = erase_box_deref_expr(&expr, &box_params);

    // Both Box deref layers erased: View(Final(Old(Var("self.2"))))
    assert_eq!(
        result,
        PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Old(
            Arc::new(var)
        )))))
    );
}

#[test]
fn test_erase_box_deref_old_non_box_param_preserved() {
    // Deref(Old(Var("self.0"))) is NOT erased when self.0 is not a Box capture
    let box_params = HashSet::from(["self.1".to_string()]);
    let expr = PureExpr::Deref(Arc::new(PureExpr::Old(Arc::new(PureExpr::Var(
        "self.0".to_string(),
        Some(ExprSort::MutRef(Box::new(ExprSort::Int))),
    )))));

    let result = erase_box_deref_expr(&expr, &box_params);

    // Unchanged — self.0 is not a Box param
    assert_eq!(result, expr);
}
