// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_if_else_simple() {
    // Basic if-else with comparison
    let expr = parse_ok("if a >= b { a } else { b }");
    assert!(matches!(expr, PureExpr::Ite(_, _, _)));

    if let PureExpr::Ite(cond, then_expr, else_expr) = expr {
        // Condition: a >= b
        assert!(matches!(cond.as_ref(), PureExpr::BinOp(_, BinOp::Ge, _)));
        // Then: a
        assert_eq!(*then_expr, PureExpr::Var("a".into(), None));
        // Else: b
        assert_eq!(*else_expr, PureExpr::Var("b".into(), None));
    }
}

#[test]
fn test_if_else_with_arithmetic() {
    let expr = parse_ok("if x > 0 { x + 1 } else { 0 }");

    if let PureExpr::Ite(ref cond, ref then_expr, ref else_expr) = expr {
        assert!(matches!(cond.as_ref(), PureExpr::BinOp(_, BinOp::Gt, _)));
        assert!(matches!(
            then_expr.as_ref(),
            PureExpr::BinOp(_, BinOp::Add, _)
        ));
        assert_eq!(else_expr.as_ref(), &PureExpr::Int(0));
    } else {
        panic!("expected Ite expression, got {expr:?}");
    }
}

#[test]
fn test_if_else_boolean_condition() {
    let expr = parse_ok("if true { 1 } else { 0 }");

    if let PureExpr::Ite(ref cond, ref then_expr, ref else_expr) = expr {
        assert_eq!(cond.as_ref(), &PureExpr::Bool(true));
        assert_eq!(then_expr.as_ref(), &PureExpr::Int(1));
        assert_eq!(else_expr.as_ref(), &PureExpr::Int(0));
    } else {
        panic!("expected Ite expression, got {expr:?}");
    }
}

#[test]
fn test_if_else_negated_condition() {
    let expr = parse_ok("if !valid { -1 } else { x }");

    if let PureExpr::Ite(ref cond, ref then_expr, ref else_expr) = expr {
        assert!(matches!(cond.as_ref(), PureExpr::UnOp(UnOp::Not, _)));
        // -1 is parsed as a negative integer literal, not UnOp::Neg
        assert_eq!(then_expr.as_ref(), &PureExpr::Int(-1));
        assert_eq!(else_expr.as_ref(), &PureExpr::Var("x".into(), None));
    } else {
        panic!("expected Ite expression, got {expr:?}");
    }
}

#[test]
fn test_if_else_nested() {
    // Nested if-else in else branch
    let expr = parse_ok("if a > b { a } else { if b > c { b } else { c } }");

    if let PureExpr::Ite(_, ref then_expr, ref else_expr) = expr {
        assert_eq!(then_expr.as_ref(), &PureExpr::Var("a".into(), None));
        assert!(matches!(else_expr.as_ref(), PureExpr::Ite(_, _, _)));
    } else {
        panic!("expected Ite expression, got {expr:?}");
    }
}

#[test]
fn test_if_without_else_produces_unit() {
    // `if cond { body }` without else evaluates to Ite(cond, body, unit)
    let expr = parse_ok("if x > 0 { x }");
    if let PureExpr::Ite(_, ref then_expr, ref else_expr) = expr {
        assert_eq!(then_expr.as_ref(), &PureExpr::Var("x".into(), None));
        // else branch is unit: tuple_0()
        assert!(
            matches!(else_expr.as_ref(), PureExpr::LogicFnCall { name, args } if args.is_empty() && name.contains("tuple")),
            "expected unit (tuple_0) in else branch, got {else_expr:?}"
        );
    } else {
        panic!("expected Ite expression, got {expr:?}");
    }
}

#[test]
fn test_if_without_else_with_statement() {
    // Pattern from cycle.rs: `if x { f(); }` — then-block contains statement
    let expr = parse_contract("if x { f(); }").unwrap();
    if let PureExpr::Ite(ref cond, ref then_expr, ref else_expr) = expr {
        assert_eq!(cond.as_ref(), &PureExpr::Var("x".into(), None));
        // f(); → discarded statement, block evaluates to unit
        assert!(
            matches!(then_expr.as_ref(), PureExpr::LogicFnCall { args, .. } if args.is_empty()),
            "expected unit from then-block with trailing semicolon, got {then_expr:?}"
        );
        // else branch is unit
        assert!(
            matches!(else_expr.as_ref(), PureExpr::LogicFnCall { args, .. } if args.is_empty()),
            "expected unit in else branch, got {else_expr:?}"
        );
    } else {
        panic!("expected Ite expression, got {expr:?}");
    }
}

#[test]
fn test_else_if_chain() {
    // else if chain: `if a { 1 } else if b { 2 } else { 3 }`
    let expr = parse_ok("if a { 1 } else if b { 2 } else { 3 }");
    if let PureExpr::Ite(_, ref then_expr, ref else_expr) = expr {
        assert_eq!(then_expr.as_ref(), &PureExpr::Int(1));
        // else branch is another Ite
        if let PureExpr::Ite(_, ref inner_then, ref inner_else) = else_expr.as_ref() {
            assert_eq!(inner_then.as_ref(), &PureExpr::Int(2));
            assert_eq!(inner_else.as_ref(), &PureExpr::Int(3));
        } else {
            panic!("expected nested Ite for else-if, got {else_expr:?}");
        }
    } else {
        panic!("expected Ite expression, got {expr:?}");
    }
}

#[test]
fn test_if_else_error_missing_then_brace() {
    let err = parse_contract("if x > 0 x else { 0 }").unwrap_err();
    assert!(
        err.message.contains('{'),
        "expected missing-brace error, got: {}",
        err.message
    );
}

// Issue #433: Tests for if-else inside old() expressions
#[test]
fn test_if_else_inside_old() {
    // old(if a > b { a } else { b })
    let expr = parse_contract("old(if a > b { a } else { b })").unwrap();
    assert!(matches!(expr, PureExpr::Old(_)));

    if let PureExpr::Old(ref inner) = expr {
        assert!(matches!(inner.as_ref(), PureExpr::Ite(_, _, _)));
    } else {
        panic!("expected Old expression, got {expr:?}");
    }
}

#[test]
fn test_old_in_if_else_branches() {
    // if old(x) > 0 { old(x) + 1 } else { 0 }
    let expr = parse_contract("if old(x) > 0 { old(x) + 1 } else { 0 }").unwrap();
    assert!(matches!(expr, PureExpr::Ite(_, _, _)));

    if let PureExpr::Ite(ref cond, ref then_expr, _) = expr {
        // Condition contains old(x)
        if let PureExpr::BinOp(left, BinOp::Gt, _) = cond.as_ref() {
            assert!(matches!(left.as_ref(), PureExpr::Old(_)));
        } else {
            panic!("expected BinOp Gt in condition, got {cond:?}");
        }
        // Then branch has old(x) + 1
        if let PureExpr::BinOp(left, BinOp::Add, _) = then_expr.as_ref() {
            assert!(matches!(left.as_ref(), PureExpr::Old(_)));
        } else {
            panic!("expected BinOp Add in then branch, got {then_expr:?}");
        }
    } else {
        panic!("expected Ite expression, got {expr:?}");
    }
}

#[test]
fn test_nested_if_else_inside_old() {
    // old(if cond { x + y } else { if z > 0 { z } else { 0 } })
    let expr = parse_contract("old(if cond { x + y } else { if z > 0 { z } else { 0 } })").unwrap();
    assert!(matches!(expr, PureExpr::Old(_)));

    if let PureExpr::Old(ref inner) = expr {
        if let PureExpr::Ite(_, _, else_branch) = inner.as_ref() {
            // Nested if-else in else branch
            assert!(matches!(else_branch.as_ref(), PureExpr::Ite(_, _, _)));
        } else {
            panic!("expected Ite inside Old, got {inner:?}");
        }
    } else {
        panic!("expected Old expression, got {expr:?}");
    }
}

/// Regression: uppercase identifier before `{` in if-condition must NOT be
/// parsed as a struct literal. Mirrors `if last == NULL { (s, None) } else { ... }`
/// from `list_reversal_lasso.rs`. (#2331)
#[test]
fn test_if_condition_uppercase_ident_not_struct_literal() {
    let expr = parse_ok("if last == NULL { x } else { y }");
    if let PureExpr::Ite(ref cond, ref then_expr, ref else_expr) = expr {
        // Condition must be `last == NULL` (equality), not a struct literal parse error
        if let PureExpr::BinOp(ref lhs, BinOp::Eq, ref rhs) = cond.as_ref() {
            assert_eq!(lhs.as_ref(), &PureExpr::Var("last".into(), None));
            assert_eq!(rhs.as_ref(), &PureExpr::Var("NULL".into(), None));
        } else {
            panic!("expected BinOp Eq in condition, got {cond:?}");
        }
        assert_eq!(then_expr.as_ref(), &PureExpr::Var("x".into(), None));
        assert_eq!(else_expr.as_ref(), &PureExpr::Var("y".into(), None));
    } else {
        panic!("expected Ite expression, got {expr:?}");
    }
}

/// Regression: bare uppercase identifier as the entire if-condition. (#2331)
#[test]
fn test_if_condition_bare_uppercase_ident() {
    let expr = parse_ok("if DONE { 1 } else { 0 }");
    if let PureExpr::Ite(ref cond, _, _) = expr {
        assert_eq!(cond.as_ref(), &PureExpr::Var("DONE".into(), None));
    } else {
        panic!("expected Ite expression, got {expr:?}");
    }
}

/// Struct literals MUST still parse outside of if-conditions. (#2331)
#[test]
fn test_struct_literal_still_parses_normally() {
    let expr = parse_ok("Point { x: 1, y: 2 }");
    assert!(
        matches!(&expr, PureExpr::LogicFnCall { name, args } if name.starts_with("Point") && args.len() == 2),
        "struct literal should parse normally, got {expr:?}"
    );
}

// --- if-let pattern tests (#1360) ---

/// `if let Some(b) = Some(true) { b } else { false }` desugars to a Match
/// with two arms: `Some(b) => b` and `_ => false`. (#1360)
#[test]
fn test_if_let_some_basic() {
    let expr = parse_ok("if let Some(b) = Some(true) { b } else { false }");
    if let PureExpr::Match { scrutinee, arms } = &expr {
        // Scrutinee: Some(true)
        assert!(
            matches!(scrutinee.as_ref(), PureExpr::LogicFnCall { name, args }
                if name == "Some" && args.len() == 1),
            "expected Some(true) scrutinee, got {scrutinee:?}"
        );
        assert_eq!(arms.len(), 2);
        // First arm: Some(b) => b
        assert!(
            matches!(&arms[0].pattern, Pattern::Constructor { name, inner: Some(_) }
                if name == "Some"),
            "expected Some(b) pattern, got {:?}",
            arms[0].pattern
        );
        assert_eq!(arms[0].body, PureExpr::Var("b".into(), None));
        // Second arm: _ => false
        assert_eq!(arms[1].pattern, Pattern::Wildcard);
        assert_eq!(arms[1].body, PureExpr::Bool(false));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

/// `if let None = x { 1 } else { 2 }` desugars to a Match. (#1360)
#[test]
fn test_if_let_none() {
    let expr = parse_ok("if let None = x { 1 } else { 2 }");
    if let PureExpr::Match { scrutinee, arms } = &expr {
        assert_eq!(scrutinee.as_ref(), &PureExpr::Var("x".into(), None));
        assert_eq!(arms.len(), 2);
        assert!(
            matches!(&arms[0].pattern, Pattern::Constructor { name, inner: None }
                if name == "None"),
            "expected None pattern, got {:?}",
            arms[0].pattern
        );
        assert_eq!(arms[0].body, PureExpr::Int(1));
        assert_eq!(arms[1].pattern, Pattern::Wildcard);
        assert_eq!(arms[1].body, PureExpr::Int(2));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

/// `if let Some(b) = expr { body }` without else gets unit in wildcard arm. (#1360)
#[test]
fn test_if_let_without_else() {
    let expr = parse_ok("if let Some(b) = x { b }");
    if let PureExpr::Match { arms, .. } = &expr {
        assert_eq!(arms.len(), 2);
        // Wildcard arm body is unit
        assert_eq!(arms[1].pattern, Pattern::Wildcard);
        assert!(
            matches!(&arms[1].body, PureExpr::LogicFnCall { args, .. } if args.is_empty()),
            "expected unit in wildcard arm, got {:?}",
            arms[1].body
        );
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

/// Regression test for the exact failing case from #1360:
/// `if let Some(b) = Some(true)` was producing parse error at position 4.
#[test]
fn test_if_let_some_verify_regression() {
    // This must parse without error — the original bug was:
    // "parse error at position 4: unexpected characters after expression"
    let result = parse_contract("if let Some(b) = Some(true) { b } else { false }");
    assert!(
        result.is_ok(),
        "if let Some(b) = Some(true) should parse, got: {}",
        result.unwrap_err()
    );
}

// --- Comprehensive if-let tests (#1360) ---

/// Basic if-let: `if let Some(x) = opt { x } else { 0 }` desugars to Match
/// with a `Some(x)` arm and a wildcard arm. (#1360)
#[test]
fn test_if_let_basic() {
    let expr = parse_ok("if let Some(x) = opt { x } else { 0 }");
    if let PureExpr::Match { scrutinee, arms } = &expr {
        // Scrutinee: opt
        assert_eq!(scrutinee.as_ref(), &PureExpr::Var("opt".into(), None));
        assert_eq!(arms.len(), 2);
        // First arm: Some(x) => x
        assert!(
            matches!(&arms[0].pattern, Pattern::Constructor { name, inner: Some(inner) }
                if name == "Some" && matches!(inner.as_ref(), Pattern::Binding(b) if b == "x")),
            "expected Some(x) pattern, got {:?}",
            arms[0].pattern
        );
        assert_eq!(arms[0].body, PureExpr::Var("x".into(), None));
        // Second arm: _ => 0
        assert_eq!(arms[1].pattern, Pattern::Wildcard);
        assert_eq!(arms[1].body, PureExpr::Int(0));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

/// If-let without else: `if let Some(x) = opt { x }` desugars to Match with
/// a unit-tuple body in the wildcard arm (matching Rust semantics). (#1360)
#[test]
fn test_if_let_no_else() {
    let expr = parse_ok("if let Some(x) = opt { x }");
    if let PureExpr::Match { scrutinee, arms } = &expr {
        assert_eq!(scrutinee.as_ref(), &PureExpr::Var("opt".into(), None));
        assert_eq!(arms.len(), 2);
        // First arm: Some(x) => x
        assert!(
            matches!(&arms[0].pattern, Pattern::Constructor { name, .. } if name == "Some"),
            "expected Some pattern, got {:?}",
            arms[0].pattern
        );
        assert_eq!(arms[0].body, PureExpr::Var("x".into(), None));
        // Second arm: _ => unit (tuple_0)
        assert_eq!(arms[1].pattern, Pattern::Wildcard);
        assert!(
            matches!(&arms[1].body, PureExpr::LogicFnCall { name, args }
                if args.is_empty() && name == &tuple_logic_fn_name(0)),
            "expected unit (tuple_0) in wildcard arm, got {:?}",
            arms[1].body
        );
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

/// Nested if-let: outer and inner both desugar to Match, producing a nested
/// `Match { ..., body: Match { ... } }` structure. (#1360)
#[test]
fn test_if_let_nested() {
    let expr = parse_ok("if let Some(x) = opt { if let Ok(y) = x { y } else { 0 } } else { 0 }");
    if let PureExpr::Match { scrutinee, arms } = &expr {
        // Outer scrutinee: opt
        assert_eq!(scrutinee.as_ref(), &PureExpr::Var("opt".into(), None));
        assert_eq!(arms.len(), 2);
        // Outer first arm body is the inner if-let, desugared to Match
        if let PureExpr::Match {
            scrutinee: inner_scrutinee,
            arms: inner_arms,
        } = &arms[0].body
        {
            // Inner scrutinee: x
            assert_eq!(inner_scrutinee.as_ref(), &PureExpr::Var("x".into(), None));
            assert_eq!(inner_arms.len(), 2);
            // Inner first arm: Ok(y) => y
            assert!(
                matches!(&inner_arms[0].pattern, Pattern::Constructor { name, .. }
                    if name == "Ok"),
                "expected Ok pattern, got {:?}",
                inner_arms[0].pattern
            );
            assert_eq!(inner_arms[0].body, PureExpr::Var("y".into(), None));
            // Inner second arm: _ => 0
            assert_eq!(inner_arms[1].pattern, Pattern::Wildcard);
            assert_eq!(inner_arms[1].body, PureExpr::Int(0));
        } else {
            panic!(
                "expected nested Match in outer then-arm, got {:?}",
                arms[0].body
            );
        }
        // Outer second arm: _ => 0
        assert_eq!(arms[1].pattern, Pattern::Wildcard);
        assert_eq!(arms[1].body, PureExpr::Int(0));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

/// Tuple pattern in if-let: `if let (a, b) = pair { a + b } else { 0 }`
/// desugars to Match with a Tuple pattern arm. (#1360)
#[test]
fn test_if_let_tuple_pattern() {
    let expr = parse_ok("if let (a, b) = pair { a + b } else { 0 }");
    if let PureExpr::Match { scrutinee, arms } = &expr {
        assert_eq!(scrutinee.as_ref(), &PureExpr::Var("pair".into(), None));
        assert_eq!(arms.len(), 2);
        // First arm: (a, b) => a + b
        assert_eq!(
            arms[0].pattern,
            Pattern::Tuple(vec![
                Pattern::Binding("a".into()),
                Pattern::Binding("b".into()),
            ])
        );
        assert!(
            matches!(&arms[0].body, PureExpr::BinOp(_, BinOp::Add, _)),
            "expected a + b in then arm, got {:?}",
            arms[0].body
        );
        // Second arm: _ => 0
        assert_eq!(arms[1].pattern, Pattern::Wildcard);
        assert_eq!(arms[1].body, PureExpr::Int(0));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

/// Wildcard pattern in if-let: `if let _ = x { 1 } else { 0 }` desugars to
/// Match with a Wildcard pattern arm (always matches). (#1360)
#[test]
fn test_if_let_wildcard() {
    let expr = parse_ok("if let _ = x { 1 } else { 0 }");
    if let PureExpr::Match { scrutinee, arms } = &expr {
        assert_eq!(scrutinee.as_ref(), &PureExpr::Var("x".into(), None));
        assert_eq!(arms.len(), 2);
        // First arm: _ => 1 (the if-let wildcard pattern)
        assert_eq!(arms[0].pattern, Pattern::Wildcard);
        assert_eq!(arms[0].body, PureExpr::Int(1));
        // Second arm: _ => 0 (the else wildcard, always added by desugaring)
        assert_eq!(arms[1].pattern, Pattern::Wildcard);
        assert_eq!(arms[1].body, PureExpr::Int(0));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}
