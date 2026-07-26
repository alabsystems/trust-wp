// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Display formatting tests for all formula types in `display.rs`.
//!
//! Coverage gap: `display.rs` (266 LOC) has zero `#[cfg(test)]` blocks and only
//! 1 external test (`display_closure_regression.rs`). These tests verify the
//! `Display` output for:
//! - `PureExpr` (all 18 variants)
//! - `Pattern` (all 5 variants)
//! - `MatchArm`
//! - `BinOp` (all 19 operators)
//! - `UnOp` (both variants)
//! - `Permission` (full, half, fractional)
//! - `Formula` (all 12 variants)
//! - `Location`, `Value`
//! - `ExprSort` (all 10 variants)

use std::{num::NonZeroU32, sync::Arc};

use trust_wp_core::formula::{
    BinOp, ExprSort, Location, MatchArm, Pattern, Permission, PureExpr, UnOp, Value,
};

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn int(v: i64) -> PureExpr {
    PureExpr::Int(v)
}

// === PureExpr Display ===

#[test]
fn display_bool_true() {
    assert_eq!(format!("{}", PureExpr::Bool(true)), "true");
}

#[test]
fn display_bool_false() {
    assert_eq!(format!("{}", PureExpr::Bool(false)), "false");
}

#[test]
fn display_int_positive() {
    assert_eq!(format!("{}", int(42)), "42");
}

#[test]
fn display_int_negative() {
    assert_eq!(format!("{}", int(-7)), "-7");
}

#[test]
fn display_var() {
    assert_eq!(format!("{}", var("x")), "x");
}

#[test]
fn display_var_with_sort_ignored() {
    // Sort annotation is not shown in Display
    let expr = PureExpr::Var("x".to_string(), Some(ExprSort::Bool));
    assert_eq!(format!("{expr}"), "x");
}

#[test]
fn display_binop() {
    let expr = PureExpr::BinOp(Arc::new(var("x")), BinOp::Add, Arc::new(int(1)));
    assert_eq!(format!("{expr}"), "(x + 1)");
}

#[test]
fn display_unop_not() {
    let expr = PureExpr::UnOp(UnOp::Not, Arc::new(var("b")));
    assert_eq!(format!("{expr}"), "!b");
}

#[test]
fn display_unop_neg() {
    let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(var("x")));
    assert_eq!(format!("{expr}"), "-x");
}

#[test]
fn display_ite() {
    let expr = PureExpr::Ite(Arc::new(var("cond")), Arc::new(int(1)), Arc::new(int(2)));
    assert_eq!(format!("{expr}"), "if cond { 1 } else { 2 }");
}

#[test]
fn display_old() {
    let expr = PureExpr::Old(Arc::new(var("x")));
    assert_eq!(format!("{expr}"), "old(x)");
}

#[test]
fn display_deref() {
    let expr = PureExpr::Deref(Arc::new(var("x")));
    assert_eq!(format!("{expr}"), "*x");
}

#[test]
fn display_final() {
    let expr = PureExpr::Final(Arc::new(var("x")));
    assert_eq!(format!("{expr}"), "^x");
}

#[test]
fn display_view() {
    let expr = PureExpr::View(Arc::new(var("v")));
    assert_eq!(format!("{expr}"), "v@");
}

#[test]
fn display_method_call_no_args() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(var("v")),
        method: "len".to_string(),
        args: vec![],
    };
    assert_eq!(format!("{expr}"), "v.len()");
}

#[test]
fn display_method_call_with_args() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(var("s")),
        method: "push_back".to_string(),
        args: vec![int(42)],
    };
    assert_eq!(format!("{expr}"), "s.push_back(42)");
}

#[test]
fn display_method_call_multiple_args() {
    let expr = PureExpr::MethodCall {
        receiver: Arc::new(var("s")),
        method: "subsequence".to_string(),
        args: vec![int(1), int(5)],
    };
    assert_eq!(format!("{expr}"), "s.subsequence(1, 5)");
}

#[test]
fn display_forall_no_sort() {
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(var("x")),
        triggers: vec![],
    };
    assert_eq!(format!("{expr}"), "forall<x: _> x");
}

#[test]
fn display_forall_with_sort() {
    let expr = PureExpr::Forall {
        var: "i".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("i")),
            BinOp::Ge,
            Arc::new(int(0)),
        )),
        triggers: vec![],
    };
    assert_eq!(format!("{expr}"), "forall<i: Int> (i >= 0)");
}

#[test]
fn display_forall_with_triggers() {
    let trigger_expr = var("x");
    let expr = PureExpr::Forall {
        var: "x".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(PureExpr::Bool(true)),
        triggers: vec![vec![trigger_expr]],
    };
    let s = format!("{expr}");
    assert!(s.starts_with("forall<x: Int> true"));
    assert!(s.contains("[triggers:"));
}

#[test]
fn display_exists_no_sort() {
    let expr = PureExpr::Exists {
        var: "y".to_string(),
        var_sort: None,
        body: Arc::new(var("y")),
        triggers: vec![],
    };
    assert_eq!(format!("{expr}"), "exists<y: _> y");
}

#[test]
fn display_exists_with_sort() {
    let expr = PureExpr::Exists {
        var: "b".to_string(),
        var_sort: Some(ExprSort::Bool),
        body: Arc::new(var("b")),
        triggers: vec![],
    };
    assert_eq!(format!("{expr}"), "exists<b: Bool> b");
}

#[test]
fn display_match() {
    let expr = PureExpr::Match {
        scrutinee: Arc::new(var("opt")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                body: var("v"),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                body: int(0),
            },
        ],
    };
    assert_eq!(format!("{expr}"), "match opt { Some(v) => v, None => 0 }");
}

#[test]
fn display_logic_fn_call_simple_name() {
    let expr = PureExpr::LogicFnCall {
        name: "my_fn".to_string(),
        args: vec![var("x"), int(1)],
    };
    assert_eq!(format!("{expr}"), "my_fn(x, 1)");
}

#[test]
fn display_logic_fn_call_qualified_name() {
    // Qualified paths should show only the last segment
    let expr = PureExpr::LogicFnCall {
        name: "crate::specs::max".to_string(),
        args: vec![var("a"), var("b")],
    };
    assert_eq!(format!("{expr}"), "max(a, b)");
}

#[test]
fn display_logic_fn_call_no_args() {
    let expr = PureExpr::LogicFnCall {
        name: "empty_seq".to_string(),
        args: vec![],
    };
    assert_eq!(format!("{expr}"), "empty_seq()");
}

#[test]
fn display_let() {
    let expr = PureExpr::Let {
        var: "x".to_string(),
        value: Arc::new(int(42)),
        body: Arc::new(var("x")),
    };
    assert_eq!(format!("{expr}"), "let x = 42; x");
}

#[test]
fn display_let_assume() {
    let expr = PureExpr::LetAssume {
        assumption: Arc::new(PureExpr::BinOp(
            Arc::new(var("x")),
            BinOp::Gt,
            Arc::new(int(0)),
        )),
        body: Arc::new(var("x")),
    };
    assert_eq!(format!("{expr}"), "assume (x > 0); x");
}

#[test]
fn display_let_obligation() {
    let expr = PureExpr::LetObligation {
        obligation: Arc::new(PureExpr::BinOp(
            Arc::new(var("n")),
            BinOp::Ge,
            Arc::new(int(0)),
        )),
        body: Arc::new(var("n")),
    };
    assert_eq!(format!("{expr}"), "obligation (n >= 0); n");
}

#[test]
fn display_closure_no_sort() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), None)],
        body: Arc::new(var("x")),
    };
    assert_eq!(format!("{expr}"), "|x| x");
}

#[test]
fn display_closure_with_sort() {
    let expr = PureExpr::Closure {
        params: vec![("x".to_string(), Some(ExprSort::Int))],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("x")),
            BinOp::Add,
            Arc::new(int(1)),
        )),
    };
    assert_eq!(format!("{expr}"), "|x: Int| (x + 1)");
}

#[test]
fn display_closure_multiple_params() {
    let expr = PureExpr::Closure {
        params: vec![
            ("a".to_string(), Some(ExprSort::Int)),
            ("b".to_string(), None),
        ],
        body: Arc::new(PureExpr::BinOp(
            Arc::new(var("a")),
            BinOp::Add,
            Arc::new(var("b")),
        )),
    };
    assert_eq!(format!("{expr}"), "|a: Int, b| (a + b)");
}

// === Pattern Display ===

#[test]
fn display_pattern_wildcard() {
    assert_eq!(format!("{}", Pattern::Wildcard), "_");
}

#[test]
fn display_pattern_binding() {
    assert_eq!(format!("{}", Pattern::Binding("x".to_string())), "x");
}

#[test]
fn display_pattern_literal() {
    assert_eq!(format!("{}", Pattern::Literal(int(42))), "42");
}

#[test]
fn display_pattern_constructor_nullary() {
    let pat = Pattern::Constructor {
        name: "None".to_string(),
        inner: None,
    };
    assert_eq!(format!("{pat}"), "None");
}

#[test]
fn display_pattern_constructor_with_inner() {
    let pat = Pattern::Constructor {
        name: "Some".to_string(),
        inner: Some(Box::new(Pattern::Binding("v".to_string()))),
    };
    assert_eq!(format!("{pat}"), "Some(v)");
}

#[test]
fn display_pattern_tuple() {
    let pat = Pattern::Tuple(vec![
        Pattern::Binding("a".to_string()),
        Pattern::Binding("b".to_string()),
    ]);
    assert_eq!(format!("{pat}"), "(a, b)");
}

#[test]
fn display_pattern_tuple_single() {
    let pat = Pattern::Tuple(vec![Pattern::Binding("x".to_string())]);
    assert_eq!(format!("{pat}"), "(x)");
}

// === MatchArm Display ===

#[test]
fn display_match_arm() {
    let arm = MatchArm {
        pattern: Pattern::Binding("x".to_string()),
        body: int(42),
    };
    assert_eq!(format!("{arm}"), "x => 42");
}

// === BinOp Display (all 19 operators) ===

#[test]
fn display_binop_all_operators() {
    let cases = [
        (BinOp::Add, "+"),
        (BinOp::Sub, "-"),
        (BinOp::Mul, "*"),
        (BinOp::Div, "/"),
        (BinOp::Mod, "%"),
        (BinOp::Shl, "<<"),
        (BinOp::Shr, ">>"),
        (BinOp::BitAnd, "&"),
        (BinOp::BitXor, "^"),
        (BinOp::BitOr, "|"),
        (BinOp::Eq, "=="),
        (BinOp::Ne, "!="),
        (BinOp::Lt, "<"),
        (BinOp::Le, "<="),
        (BinOp::Gt, ">"),
        (BinOp::Ge, ">="),
        (BinOp::And, "&&"),
        (BinOp::Or, "||"),
        (BinOp::Implies, "==>"),
    ];
    for (op, expected) in &cases {
        assert_eq!(format!("{op}"), *expected, "BinOp::{op:?} mismatch");
    }
}

// === UnOp Display ===

#[test]
fn display_unop_all() {
    assert_eq!(format!("{}", UnOp::Not), "!");
    assert_eq!(format!("{}", UnOp::Neg), "-");
}

// === Permission Display ===

#[test]
fn display_permission_full() {
    let perm = Permission {
        numerator: 1,
        denominator: NonZeroU32::new(1).unwrap(),
    };
    assert_eq!(format!("{perm}"), "full");
}

#[test]
fn display_permission_half() {
    let perm = Permission {
        numerator: 1,
        denominator: NonZeroU32::new(2).unwrap(),
    };
    assert_eq!(format!("{perm}"), "half");
}

#[test]
fn display_permission_fractional() {
    let perm = Permission {
        numerator: 3,
        denominator: NonZeroU32::new(4).unwrap(),
    };
    assert_eq!(format!("{perm}"), "3/4");
}

// === Location & Value Display ===

#[test]
fn display_location() {
    let loc = Location("heap_addr".to_string());
    assert_eq!(format!("{loc}"), "heap_addr");
}

#[test]
fn display_value_expr() {
    let val = Value::Expr(int(99));
    assert_eq!(format!("{val}"), "99");
}

#[test]
fn display_value_unknown() {
    assert_eq!(format!("{}", Value::Unknown), "_");
}

// === ExprSort Display ===

#[test]
fn display_expr_sort_simple_variants() {
    assert_eq!(format!("{}", ExprSort::Bool), "Bool");
    assert_eq!(format!("{}", ExprSort::Int), "Int");
    assert_eq!(format!("{}", ExprSort::Seq), "Seq");
    assert_eq!(format!("{}", ExprSort::Unit), "()");
    assert_eq!(format!("{}", ExprSort::FMap), "FMap");
    assert_eq!(format!("{}", ExprSort::Float), "Float");
}

#[test]
fn display_expr_sort_tuple() {
    assert_eq!(format!("{}", ExprSort::Tuple(2)), "Tuple(2)");
    assert_eq!(format!("{}", ExprSort::Tuple(0)), "Tuple(0)");
}

#[test]
fn display_expr_sort_ref() {
    let sort = ExprSort::Ref(Box::new(ExprSort::Int));
    assert_eq!(format!("{sort}"), "&Int");
}

#[test]
fn display_expr_sort_ref_nested() {
    let sort = ExprSort::Ref(Box::new(ExprSort::Ref(Box::new(ExprSort::Bool))));
    assert_eq!(format!("{sort}"), "&&Bool");
}

#[test]
fn display_expr_sort_mut_ref() {
    let sort = ExprSort::MutRef(Box::new(ExprSort::Int));
    assert_eq!(format!("{sort}"), "&mut Int");
}

#[test]
fn display_expr_sort_datatype() {
    use trust_wp_core::formula::intern_sort_name;
    let id = intern_sort_name("MyStruct");
    let sort = ExprSort::Datatype(id);
    assert_eq!(format!("{sort}"), "Datatype(MyStruct)");
}

#[test]
fn display_expr_sort_type_param() {
    use trust_wp_core::formula::intern_sort_name;
    let id = intern_sort_name("T");
    let sort = ExprSort::TypeParam(id);
    assert_eq!(format!("{sort}"), "TypeParam(T)");
}

// === Formula Display ===

#[test]
fn display_formula_true_false() {
    use trust_wp_core::formula::Formula;
    assert_eq!(format!("{}", Formula::True), "true");
    assert_eq!(format!("{}", Formula::False), "false");
}

#[test]
fn display_formula_pure() {
    use trust_wp_core::formula::Formula;
    let f = Formula::Pure(var("x"));
    assert_eq!(format!("{f}"), "x");
}

#[test]
fn display_formula_points_to() {
    use trust_wp_core::formula::Formula;
    let perm = Permission {
        numerator: 1,
        denominator: NonZeroU32::new(1).unwrap(),
    };
    let f = Formula::PointsTo {
        location: Location("addr".to_string()),
        value: Value::Expr(int(42)),
        permission: perm,
    };
    assert_eq!(format!("{f}"), "addr ↦[full] 42");
}

#[test]
fn display_formula_mut_borrow() {
    use trust_wp_core::formula::Formula;
    let f = Formula::MutBorrow {
        var: "r".to_string(),
        current: Arc::new(var("c")),
        final_val: Arc::new(var("f")),
        id: Arc::new(int(7)),
    };
    assert_eq!(format!("{f}"), "borrow(r: *=c, ^=f, id=7)");
}

#[test]
fn display_formula_sep_conj() {
    use trust_wp_core::formula::Formula;
    let f = Formula::SepConj(Arc::new(Formula::True), Arc::new(Formula::False));
    assert_eq!(format!("{f}"), "(true * false)");
}

#[test]
fn display_formula_and() {
    use trust_wp_core::formula::Formula;
    let f = Formula::And(Arc::new(Formula::True), Arc::new(Formula::False));
    assert_eq!(format!("{f}"), "(true ∧ false)");
}

#[test]
fn display_formula_or() {
    use trust_wp_core::formula::Formula;
    let f = Formula::Or(Arc::new(Formula::True), Arc::new(Formula::False));
    assert_eq!(format!("{f}"), "(true ∨ false)");
}

#[test]
fn display_formula_implies() {
    use trust_wp_core::formula::Formula;
    let f = Formula::Implies(
        Arc::new(Formula::Pure(var("a"))),
        Arc::new(Formula::Pure(var("b"))),
    );
    assert_eq!(format!("{f}"), "(a → b)");
}

#[test]
fn display_formula_magic_wand() {
    use trust_wp_core::formula::Formula;
    let f = Formula::MagicWand(Arc::new(Formula::True), Arc::new(Formula::Pure(var("x"))));
    assert_eq!(format!("{f}"), "(true -* x)");
}

#[test]
fn display_formula_exists() {
    use trust_wp_core::formula::Formula;
    let f = Formula::Exists {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(Formula::Pure(var("x"))),
        triggers: vec![],
    };
    assert_eq!(format!("{f}"), "∃x. x");
}

#[test]
fn display_formula_forall() {
    use trust_wp_core::formula::Formula;
    let f = Formula::Forall {
        var: "x".to_string(),
        var_sort: None,
        body: Arc::new(Formula::Pure(var("x"))),
        triggers: vec![],
    };
    assert_eq!(format!("{f}"), "∀x. x");
}
