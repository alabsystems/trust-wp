// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::formula::Pattern;

#[test]
fn test_match_simple_option() {
    // match *self { Some(v) => result == v, None => result == default }
    let expr = parse_contract("match *self { Some(v) => result == v, None => result == default }")
        .unwrap();

    if let PureExpr::Match {
        ref scrutinee,
        ref arms,
    } = expr
    {
        // Check scrutinee is *self
        assert!(matches!(scrutinee.as_ref(), PureExpr::Deref(_)));

        // Check we have 2 arms
        assert_eq!(arms.len(), 2);

        // First arm: Some(v) => ...
        assert!(matches!(
            &arms[0].pattern,
            Pattern::Constructor { name, inner: Some(_) } if name == "Some"
        ));

        // Second arm: None => ...
        assert!(matches!(
            &arms[1].pattern,
            Pattern::Constructor { name, inner: None } if name == "None"
        ));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

#[test]
fn test_match_constructor_multiple_args() {
    let expr = parse_contract("match l { Cons(a, l) => a, Nil => 0 }").unwrap();

    if let PureExpr::Match { ref arms, .. } = expr {
        assert_eq!(arms.len(), 2);
        assert_eq!(
            arms[0].pattern,
            Pattern::Constructor {
                name: "Cons".into(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("a".into()),
                    Pattern::Binding("l".into()),
                ]))),
            }
        );
        assert!(matches!(
            &arms[1].pattern,
            Pattern::Constructor { name, inner: None } if name == "Nil"
        ));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

#[test]
fn test_match_constructor_explicit_zero_args_normalizes_to_unit() {
    let expr = parse_contract("match l { Nil() => 0, Cons(a, l) => a }").unwrap();

    if let PureExpr::Match { ref arms, .. } = expr {
        assert_eq!(arms.len(), 2);
        assert!(matches!(
            &arms[0].pattern,
            Pattern::Constructor { name, inner: None } if name == "Nil"
        ));
        assert_eq!(
            arms[1].pattern,
            Pattern::Constructor {
                name: "Cons".into(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("a".into()),
                    Pattern::Binding("l".into()),
                ]))),
            }
        );
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

#[test]
fn test_match_qualified_path_constructor() {
    // Path-qualified constructors like OwnResult::Ok(s) in match patterns (#939)
    let expr = parse_contract(
        "match (self, result) { (OwnResult::Ok(s), OwnResult::Ok(r)) => true, _ => false }",
    )
    .unwrap();

    if let PureExpr::Match { ref arms, .. } = expr {
        assert_eq!(arms.len(), 2);
        // First arm: (OwnResult::Ok(s), OwnResult::Ok(r))
        if let Pattern::Tuple(ref elements) = arms[0].pattern {
            assert_eq!(elements.len(), 2);
            assert_eq!(
                elements[0],
                Pattern::Constructor {
                    name: "OwnResult::Ok".into(),
                    inner: Some(Box::new(Pattern::Binding("s".into()))),
                }
            );
            assert_eq!(
                elements[1],
                Pattern::Constructor {
                    name: "OwnResult::Ok".into(),
                    inner: Some(Box::new(Pattern::Binding("r".into()))),
                }
            );
        } else {
            panic!("expected Tuple pattern, got {:?}", arms[0].pattern);
        }
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

#[test]
fn test_match_qualified_path_unit_constructor() {
    // Qualified unit constructor without arguments (e.g., std::option::None)
    let expr = parse_contract("match x { module::None => 0, module::Some(v) => v }").unwrap();

    if let PureExpr::Match { ref arms, .. } = expr {
        assert_eq!(arms.len(), 2);
        assert!(matches!(
            &arms[0].pattern,
            Pattern::Constructor { name, inner: None } if name == "module::None"
        ));
        assert_eq!(
            arms[1].pattern,
            Pattern::Constructor {
                name: "module::Some".into(),
                inner: Some(Box::new(Pattern::Binding("v".into()))),
            }
        );
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

#[test]
fn test_match_binary_scrutinee() {
    // match on a full expression, not just unary. Pearlite does not support
    // matching integer literals, so use a constructor pattern instead.
    let expr = parse_ok("match Some(x + 1) { Some(y) => y, None => 0 }");

    if let PureExpr::Match {
        ref scrutinee,
        ref arms,
    } = expr
    {
        assert!(matches!(scrutinee.as_ref(), PureExpr::LogicFnCall { .. }));
        assert_eq!(arms.len(), 2);
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

#[test]
fn test_match_wildcard_pattern() {
    // Bool-literal patterns remain supported (only Int-literal patterns are
    // rejected as Pearlite-unsupported).
    let expr = parse_ok("match x { true => 1, _ => 0 }");

    if let PureExpr::Match { ref arms, .. } = expr {
        assert_eq!(arms.len(), 2);
        assert!(matches!(
            &arms[0].pattern,
            Pattern::Literal(PureExpr::Bool(true))
        ));
        assert!(matches!(&arms[1].pattern, Pattern::Wildcard));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

#[test]
fn test_match_variable_binding() {
    let expr = parse_ok("match x { y => y + 1 }");

    if let PureExpr::Match { ref arms, .. } = expr {
        assert_eq!(arms.len(), 1);
        assert!(matches!(&arms[0].pattern, Pattern::Binding(name) if name == "y"));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

#[test]
fn test_match_alias_and_box_pattern() {
    let expr = parse_ok("match x { whole @ Some(box v) => whole, _ => fallback }");

    if let PureExpr::Match { ref arms, .. } = expr {
        assert_eq!(arms.len(), 2);
        assert_eq!(
            arms[0].pattern,
            Pattern::Alias {
                alias: "whole".to_string(),
                pattern: Box::new(Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                }),
            }
        );
        assert!(matches!(arms[1].pattern, Pattern::Wildcard));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

#[test]
fn test_match_boolean_literals() {
    let expr = parse_ok("match b { true => 1, false => 0 }");

    if let PureExpr::Match { ref arms, .. } = expr {
        assert_eq!(arms.len(), 2);
        assert!(matches!(
            &arms[0].pattern,
            Pattern::Literal(PureExpr::Bool(true))
        ));
        assert!(matches!(
            &arms[1].pattern,
            Pattern::Literal(PureExpr::Bool(false))
        ));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

#[test]
fn test_match_in_comparison() {
    // Match expression used in comparison
    let expr = parse_contract("match x { Some(v) => v, None => 0 } > 0").unwrap();

    // Should be a comparison with match on the left
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Gt, _) if matches!(l.as_ref(), PureExpr::Match { .. })
    ));
}

#[test]
fn test_match_trailing_comma() {
    // Allow trailing comma. Bool literals are supported as match patterns;
    // Int literals are rejected separately (Pearlite limitation).
    let expr = parse_ok("match x { true => false, false => true, }");

    if let PureExpr::Match { ref arms, .. } = expr {
        assert_eq!(arms.len(), 2);
    } else {
        panic!("expected Match expression, got {expr:?}");
    }
}

#[test]
fn test_match_error_empty_arms() {
    let err = parse_contract("match x { }").unwrap_err();
    assert!(
        err.message.contains("at least one arm"),
        "expected empty-arms error, got: {}",
        err.message
    );
}

#[test]
fn test_match_error_missing_arrow() {
    // Use a Bool-literal pattern so the missing-arrow path is exercised
    // before the Pearlite int-literal-pattern rejection fires.
    let err = parse_contract("match x { true: false }").unwrap_err();
    assert!(
        err.message.contains("'=>'"),
        "expected missing-arrow error, got: {}",
        err.message
    );
}

#[test]
fn test_match_error_missing_brace() {
    let err = parse_contract("match x 0 => true }").unwrap_err();
    assert!(
        err.message.contains("'{'"),
        "expected missing-brace error, got: {}",
        err.message
    );
}

#[test]
fn test_match_underscore_prefixed_binding() {
    // _unused should be treated as a binding, not wildcard
    let expr = parse_ok("match x { _unused => 0 }");

    if let PureExpr::Match { ref arms, .. } = expr {
        assert_eq!(arms.len(), 1);
        // _unused should be parsed as Binding, not Wildcard
        assert!(matches!(&arms[0].pattern, Pattern::Binding(name) if name == "_unused"));
    } else {
        panic!("expected Match expression, got {expr:?}");
    }

    // __x (double underscore) should also be a binding
    let expr2 = parse_ok("match x { __x => __x + 1 }");

    if let PureExpr::Match { ref arms, .. } = expr2 {
        assert_eq!(arms.len(), 1);
        assert!(matches!(&arms[0].pattern, Pattern::Binding(name) if name == "__x"));
    } else {
        panic!("expected Match expression, got {expr2:?}");
    }
}

#[test]
fn test_match_block_body_with_trailing_comma() {
    // Block body with trailing comma — should parse normally
    let expr = parse_contract("match x { Some(v) => { v + 1 }, None => 0 }").unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
    assert!(matches!(&arms[0].pattern, Pattern::Constructor { .. }));
    assert!(matches!(&arms[1].pattern, Pattern::Constructor { .. }));
}

#[test]
fn test_match_block_body_no_trailing_comma() {
    // Block body WITHOUT trailing comma — Rust allows this (#1328)
    let expr = parse_contract("match x { Some(v) => { v + 1 } None => 0 }").unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
    assert!(matches!(&arms[0].pattern, Pattern::Constructor { .. }));
    assert!(matches!(&arms[1].pattern, Pattern::Constructor { .. }));
}

#[test]
fn test_match_block_body_if_else_inside() {
    // Block body containing if-else — the block consumes its own braces
    let expr =
        parse_contract("match x { Some(v) => { if v > 0 { v } else { 0 } }, None => 0 }").unwrap();
    assert!(
        matches!(expr, PureExpr::Match { ref arms, .. } if arms.len() == 2),
        "expected Match with 2 arms, got {expr:?}"
    );
}

#[test]
fn test_match_last_arm_block_body() {
    // Last arm is block body with no trailing comma
    let expr = parse_contract("match x { None => 0, Some(v) => { v + 1 } }").unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
    assert!(matches!(&arms[0].pattern, Pattern::Constructor { .. }));
    assert!(matches!(&arms[1].pattern, Pattern::Constructor { .. }));
}

#[test]
fn test_match_block_body_method_call_chain() {
    // Pattern from take_first_mut.rs ensures clause: block body with method calls
    // match result { Some(r) => { r.len() > 0 && r.len() > 0 } None => true }
    let expr =
        parse_contract("match result { Some(r) => { r.len() > 0 && r.len() > 0 } None => true }")
            .unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
}

#[test]
fn test_match_block_body_nested_match_body() {
    // Nested match inside block body arm (from derive_macros/mixed.rs pattern)
    // Expr::Add(e1, e2) => { f(e1) } is a block-body arm
    let expr =
        parse_contract("match self { Var(v) => f(v), Add(e1, e2) => { g(e1, e2) } }").unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
}

#[test]
fn test_match_block_body_recursive_call() {
    // Pattern from binary_search_list.rs: block body with if-else and recursive calls
    // match self { Cons(t, ls) => { if ix == 0 { t } else { ls.get(ix - 1) } } Nil => None }
    let expr = parse_contract(
        "match self { Cons(t, ls) => { if ix == 0 { Some(t) } else { ls.get(ix - 1) } } Nil => None }",
    )
    .unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
}

#[test]
fn test_recursive_method_call_ast_inspection() {
    // Verify the AST structure of a recursive method call inside a match arm.
    // The else-branch `ls.get(ix - 1)` should parse as MethodCall with correct
    // receiver, method name, and argument subtree.
    let expr = parse_ok(
        "match self { Cons(t, ls) => { if ix == 0 { Some(t) } else { ls.get(ix - 1) } } Nil => None }",
    );
    let PureExpr::Match { ref arms, .. } = expr else {
        panic!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);

    // First arm: Cons(t, ls) => if-then-else
    assert!(matches!(
        &arms[0].pattern,
        Pattern::Constructor { name, .. } if name == "Cons"
    ));
    let PureExpr::Ite(ref cond, ref then_branch, ref else_branch) = arms[0].body else {
        panic!("expected Ite in first arm body, got {:?}", arms[0].body);
    };

    // Condition: ix == 0
    assert!(matches!(
        cond.as_ref(),
        PureExpr::BinOp(lhs, BinOp::Eq, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(n, _) if n == "ix")
            && matches!(rhs.as_ref(), PureExpr::Int(0))
    ));

    // Then-branch: Some(t)
    assert!(matches!(
        then_branch.as_ref(),
        PureExpr::LogicFnCall { name, args }
            if name == "Some" && args.len() == 1
            && matches!(&args[0], PureExpr::Var(n, _) if n == "t")
    ));

    // Else-branch: ls.get(ix - 1) — the recursive call
    let PureExpr::MethodCall {
        ref receiver,
        ref method,
        ref args,
    } = **else_branch
    else {
        panic!("expected MethodCall in else-branch, got {else_branch:?}");
    };
    assert!(matches!(receiver.as_ref(), PureExpr::Var(n, _) if n == "ls"));
    assert_eq!(method, "get");
    assert_eq!(args.len(), 1);
    assert!(matches!(
        &args[0],
        PureExpr::BinOp(lhs, BinOp::Sub, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(n, _) if n == "ix")
            && matches!(rhs.as_ref(), PureExpr::Int(1))
    ));
}

#[test]
fn test_mutual_recursion_nested_call_ast() {
    // Mutual recursion pattern: f(g(x)) where nested calls must preserve
    // function names and argument structure through the AST.
    let expr = parse_ok("f(g(x))");
    let PureExpr::LogicFnCall { ref name, ref args } = expr else {
        panic!("expected LogicFnCall, got {expr:?}");
    };
    assert_eq!(name, "f");
    assert_eq!(args.len(), 1);
    let PureExpr::LogicFnCall {
        name: ref inner_name,
        args: ref inner_args,
    } = args[0]
    else {
        panic!("expected nested LogicFnCall, got {:?}", args[0]);
    };
    assert_eq!(inner_name, "g");
    assert_eq!(inner_args.len(), 1);
    assert!(matches!(&inner_args[0], PureExpr::Var(n, _) if n == "x"));
}

#[test]
fn test_deeply_nested_recursive_calls_tree_structure() {
    // Deep recursive call nesting: f(f(f(x))) must produce a three-level
    // LogicFnCall tree, each with name "f" and one argument.
    let expr = parse_ok("f(f(f(x)))");

    // Level 1: f(...)
    let PureExpr::LogicFnCall { ref name, ref args } = expr else {
        panic!("expected LogicFnCall at level 1, got {expr:?}");
    };
    assert_eq!(name, "f");
    assert_eq!(args.len(), 1);

    // Level 2: f(...)
    let PureExpr::LogicFnCall {
        name: ref name2,
        args: ref args2,
    } = args[0]
    else {
        panic!("expected LogicFnCall at level 2, got {:?}", args[0]);
    };
    assert_eq!(name2, "f");
    assert_eq!(args2.len(), 1);

    // Level 3: f(x)
    let PureExpr::LogicFnCall {
        name: ref name3,
        args: ref args3,
    } = args2[0]
    else {
        panic!("expected LogicFnCall at level 3, got {:?}", args2[0]);
    };
    assert_eq!(name3, "f");
    assert_eq!(args3.len(), 1);
    assert!(matches!(&args3[0], PureExpr::Var(n, _) if n == "x"));
}

#[test]
fn test_match_if_else_arm_body_no_comma() {
    // match arm body is if-else (no wrapping block), no trailing comma
    // Rust allows this: `pattern => if cond { x } else { y } NextPattern => ...`
    let expr =
        parse_contract("match x { Some(v) => if v > 0 { v } else { 0 } None => 0 }").unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
}

#[test]
fn test_match_nested_match_arm_body_no_comma() {
    // match arm body is a nested match (no wrapping block), no trailing comma
    let expr =
        parse_contract("match x { Some(v) => match v { A => 1, B => 2 } None => 0 }").unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
}

// Struct pattern tests (#1328)

#[test]
fn test_match_struct_pattern_shorthand() {
    // Sum::B { b } => ... (shorthand field binding)
    let expr = parse_contract("match self { Sum::A(a) => a, Sum::B { b } => b }").unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
    // First arm: positional constructor
    assert!(matches!(
        &arms[0].pattern,
        Pattern::Constructor { name, inner: Some(_) } if name == "Sum::A"
    ));
    // Second arm: struct pattern desugared to Constructor with field names
    // encoded in name. (#1819)
    assert!(matches!(
        &arms[1].pattern,
        Pattern::Constructor { name, inner: Some(inner) }
            if name == "Sum::B{b}" && matches!(inner.as_ref(), Pattern::Binding(b) if b == "b")
    ));
}

#[test]
fn test_match_struct_pattern_explicit_field() {
    // Pair { a: x, b: y } => x + y
    let expr = parse_ok("match p { Pair { a: x, b: y } => x + y }");
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 1);
    // Field names encoded in constructor name for reordering. (#1819)
    assert!(matches!(
        &arms[0].pattern,
        Pattern::Constructor { name, inner: Some(inner) }
            if name == "Pair{a,b}" && matches!(inner.as_ref(), Pattern::Tuple(fields) if fields.len() == 2)
    ));
}

#[test]
fn test_match_struct_pattern_mixed_with_positional() {
    // Mixed match arms: struct pattern + positional constructor
    // From derive_macros/mixed.rs: Sum::A(a) and Sum::B { b }
    let expr = parse_contract(
        "match self { Sum::A(a) => Sum::A(a.deep_model()), Sum::B { b } => Sum::B { b: b.deep_model() } }",
    )
    .unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
    // First arm body: constructor call
    assert!(matches!(&arms[0].body, PureExpr::LogicFnCall { name, .. } if name == "Sum::A"));
    // Second arm body: struct literal desugared to LogicFnCall with field name encoding (#1819)
    assert!(matches!(&arms[1].body, PureExpr::LogicFnCall { name, .. } if name == "Sum::B{b}"));
}

#[test]
fn test_match_struct_literal_body() {
    // Struct literal as arm body: ListDeepModel { elem: ..., tail: ... }
    // From derive_macros/mixed.rs line 74
    let expr =
        parse_contract("ListDeepModel { elem: self.elem.deep_model(), tail: None }").unwrap();
    // Field names encoded for reordering (#1819)
    assert!(matches!(&expr, PureExpr::LogicFnCall { name, args }
        if name == "ListDeepModel{elem,tail}" && args.len() == 2));
}

#[test]
fn test_match_struct_literal_shorthand() {
    // Struct literal with shorthand fields: Foo { x }
    let expr = parse_ok("Foo { x }");
    // Field name encoded in constructor name (#1819)
    assert!(matches!(&expr, PureExpr::LogicFnCall { name, args }
        if name == "Foo{x}" && args.len() == 1
        && matches!(&args[0], PureExpr::Var(v, None) if v == "x")));
}

#[test]
fn test_match_struct_pattern_nested_match_in_field() {
    // From derive_macros/mixed.rs line 76-79: match inside struct literal field
    let expr = parse_contract(
        "ListDeepModel { elem: x, tail: match self.tail { None => None, Some(t) => Some(t) } }",
    )
    .unwrap();
    // Field names encoded for reordering (#1819)
    assert!(matches!(&expr, PureExpr::LogicFnCall { name, args }
        if name == "ListDeepModel{elem,tail}" && args.len() == 2
        && matches!(&args[1], PureExpr::Match { .. })));
}

#[test]
fn test_match_take_first_mut_ensures() {
    // From take_first_mut.rs ensures clause: match with view (@) and final (^) operators
    let expr = parse_contract(
        "match result { Some(r) => { *r == x && ^r == y } None => x@ == Seq::empty() }",
    )
    .unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
    assert!(matches!(
        &arms[0].pattern,
        Pattern::Constructor { name, inner: Some(_) } if name == "Some"
    ));
    assert!(matches!(
        &arms[1].pattern,
        Pattern::Constructor { name, inner: None } if name == "None"
    ));
}

#[test]
fn test_match_deep_model_enum_full() {
    // Full derive_macros/mixed.rs Sum DeepModel impl
    let expr = parse_contract(
        "match self { Sum::A(a) => Sum::A(a.deep_model()), Sum::B { b } => Sum::B { b: b.deep_model() } }",
    )
    .unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
    // Sum::A(a) positional pattern
    assert!(matches!(
        &arms[0].pattern,
        Pattern::Constructor { name, inner: Some(_) } if name == "Sum::A"
    ));
    // Sum::B { b } struct pattern — field names encoded (#1819)
    assert!(matches!(
        &arms[1].pattern,
        Pattern::Constructor { name, inner: Some(inner) }
            if name == "Sum::B{b}" && matches!(inner.as_ref(), Pattern::Binding(b) if b == "b")
    ));
    // Sum::A(...) expression body (positional — no field encoding)
    assert!(matches!(&arms[0].body, PureExpr::LogicFnCall { name, args }
        if name == "Sum::A" && args.len() == 1));
    // Sum::B { b: ... } struct literal body — field name encoded (#1819)
    assert!(matches!(&arms[1].body, PureExpr::LogicFnCall { name, args }
        if name == "Sum::B{b}" && args.len() == 1));
}

#[test]
fn test_match_expr_add_block_body() {
    // From derive_macros/mixed.rs Expr DeepModel: block body in last arm
    let expr = parse_contract(
        "match self { Expr::Var(v) => ExprDeepModel::Var(v.deep_model()), Expr::Add(e1, e2) => { ExprDeepModel::Add(f(e1), f(e2)) } }",
    )
    .unwrap();
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
}

// ====================================================================
// Struct field name encoding regression tests (#1819)
// ====================================================================

/// Regression: struct literal with reordered fields must encode field names
/// so the driver can reorder to canonical order.
#[test]
fn test_struct_literal_encodes_field_names() {
    // Point { y: 1, x: 0 } — fields in non-canonical order
    let expr = parse_ok("Point { y: 1, x: 0 }");
    match &expr {
        PureExpr::LogicFnCall { name, args } => {
            // Field names encoded: "Point{y,x}" preserving user order
            assert_eq!(name, "Point{y,x}");
            assert_eq!(args.len(), 2);
            assert_eq!(args[0], PureExpr::Int(1)); // y's value
            assert_eq!(args[1], PureExpr::Int(0)); // x's value
        }
        other => panic!("expected LogicFnCall, got {other:?}"),
    }
}

/// Regression: struct pattern with reordered fields must encode field names.
#[test]
fn test_struct_pattern_encodes_field_names() {
    let expr = parse_ok("match p { Point { y, x } => x + y }");
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 1);
    match &arms[0].pattern {
        Pattern::Constructor { name, inner } => {
            assert_eq!(name, "Point{y,x}");
            // Two fields -> Tuple inner
            assert!(matches!(inner.as_deref(), Some(Pattern::Tuple(fields)) if fields.len() == 2));
        }
        other => panic!("expected Constructor, got {other:?}"),
    }
}

/// Regression: struct literal with canonical field order still encodes names.
#[test]
fn test_struct_literal_canonical_order_still_encodes() {
    let expr = parse_ok("Point { x: 0, y: 1 }");
    match &expr {
        PureExpr::LogicFnCall { name, args } => {
            assert_eq!(name, "Point{x,y}");
            assert_eq!(args.len(), 2);
            assert_eq!(args[0], PureExpr::Int(0));
            assert_eq!(args[1], PureExpr::Int(1));
        }
        other => panic!("expected LogicFnCall, got {other:?}"),
    }
}

/// Regression: positional constructors (e.g., Some(x)) are NOT affected.
#[test]
fn test_positional_constructor_not_encoded() {
    let expr = parse_ok("match x { Some(v) => v, None => 0 }");
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    // Positional constructor — no field encoding
    assert!(matches!(
        &arms[0].pattern,
        Pattern::Constructor { name, .. } if name == "Some"
    ));
}

/// Reference patterns `&pat` are transparent in the logical model.
/// Creusot's bdd.rs uses `Bdd(&If { childt, childf, .. }, _)` to match
/// through a reference field. The `&` should be consumed and the inner
/// pattern parsed (mirroring `box`-pattern handling).
#[test]
fn test_match_reference_pattern_transparent() {
    let expr = parse_ok("match v { &x => x, _ => 0 }");
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
    // First arm: `&x` parses as just `x` binding
    assert!(matches!(&arms[0].pattern, Pattern::Binding(name) if name == "x"));
}

/// `&mut pat` is also transparent.
#[test]
fn test_match_reference_mut_pattern_transparent() {
    let expr = parse_ok("match v { &mut x => x, _ => 0 }");
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert!(matches!(&arms[0].pattern, Pattern::Binding(name) if name == "x"));
}

/// Reference pattern inside tuple-struct constructor: `Bdd(&If { v, .. }, _)`.
/// The `&` should be consumed so the inner struct pattern parses normally.
#[test]
fn test_match_tuple_ctor_with_reference_struct_pattern() {
    let expr = parse_ok("match a { Bdd(&If { childt, childf, .. }, _) => childt, _ => 0u32 }");
    let PureExpr::Match { ref arms, .. } = expr else {
        unreachable!("expected Match, got {expr:?}");
    };
    assert_eq!(arms.len(), 2);
    // First arm should parse as `Bdd(<inner_pattern>, _)`
    let Pattern::Constructor {
        name,
        inner: Some(inner),
    } = &arms[0].pattern
    else {
        panic!(
            "expected Constructor for first arm, got {:?}",
            arms[0].pattern
        );
    };
    assert_eq!(name, "Bdd");
    // Inner is a tuple of (struct-pat, wildcard)
    let Pattern::Tuple(fields) = inner.as_ref() else {
        panic!("expected Tuple inner pattern, got {inner:?}");
    };
    assert_eq!(fields.len(), 2);
    // First field: struct pattern `If { childt, childf, .. }`
    assert!(matches!(
        &fields[0],
        Pattern::Constructor { name, .. } if name == "If"
    ));
    // Second field: wildcard
    assert!(matches!(&fields[1], Pattern::Wildcard));
}

// ====================================================================
// Character literal patterns are UNSUPPORTED (Creusot-faithful rejection)
// ====================================================================
//
// Creusot rejects `match` on `char` outright with "match on char is currently
// unsupported" (reference/creusot/tests/should_fail/unsupported/char_pattern.rs).
// The root cause is the same Pearlite limitation the int-literal-pattern
// rejection enforces: a char-literal pattern can only lower to an integer
// match on the Unicode codepoint, and Pearlite does not support matching `Int`
// literals. trust-wp therefore fails closed: the parser drives the full
// char-literal parser (so malformed char literals still surface their precise
// parse errors), then rejects the resulting char-literal pattern. Accepting a
// codepoint-lowered char pattern would be unsound w.r.t. supported
// pattern-matching semantics. (char-pattern soundness 2026-06-02)

/// Asserts that `input` is rejected with the char-pattern unsupported error.
#[track_caller]
fn assert_char_pattern_rejected(input: &str) {
    let err = parse_contract(input)
        .expect_err(&format!("char-literal pattern must be rejected: {input:?}"));
    assert!(
        err.message
            .contains("match on char is currently unsupported"),
        "expected char-pattern unsupported error, got: {}",
        err.message
    );
}

/// ASCII char literal patterns (`'a'`, `'z'`) are rejected: char matching is
/// unsupported (Pearlite cannot match the lowered codepoint Int literal).
#[test]
fn test_match_char_literal_pattern_ascii() {
    assert_char_pattern_rejected("match c { 'a' => 1, 'z' => 2, _ => 0 }");
}

/// Escape-sequence char literals (`\n`, `\t`, `\\`, `\'`, `\0`) parse cleanly
/// through `parse_char_literal` but are then rejected as unsupported char
/// patterns — the escape handler runs first, so a WELL-FORMED escape reaches
/// the char-pattern rejection (not an escape parse error).
#[test]
fn test_match_char_literal_pattern_escapes() {
    for input in [
        "match c { '\\n' => 1, _ => 0 }",
        "match c { '\\t' => 1, _ => 0 }",
        "match c { '\\\\' => 1, _ => 0 }",
        "match c { '\\'' => 1, _ => 0 }",
        "match c { '\\0' => 1, _ => 0 }",
    ] {
        assert_char_pattern_rejected(input);
    }
}

/// A well-formed Unicode escape `\u{XXXX}` char pattern parses past the escape
/// handler and is then rejected as an unsupported char pattern.
#[test]
fn test_match_char_literal_pattern_unicode_escape() {
    assert_char_pattern_rejected("match c { '\\u{1F600}' => 1, _ => 0 }");
}

/// Char literals are rejected at ANY pattern position, including nested inside
/// a tuple pattern: `(true, 'x')`.
#[test]
fn test_match_char_literal_pattern_inside_tuple() {
    assert_char_pattern_rejected("match p { (true, 'x') => 1, _ => 0 }");
}

/// Char literals nested inside a constructor pattern (`Some('y')`) are also
/// rejected.
#[test]
fn test_match_char_literal_pattern_inside_constructor() {
    assert_char_pattern_rejected("match o { Some('y') => 1, None => 0, _ => 2 }");
}

/// Negative: an unterminated char literal in pattern position must surface a
/// parse error rather than silently succeeding. Without the closing quote,
/// `parse_char_literal` reports "expected closing '" up through `parse_pattern`.
#[test]
fn test_match_char_literal_pattern_unterminated_errors() {
    let err = parse_contract("match c { 'a => 1, _ => 0 }");
    assert!(
        err.is_err(),
        "expected parse error for unterminated 'a, got Ok: {err:?}"
    );
}

/// Negative: an unknown escape (`\q`) inside a char-pattern must error.
#[test]
fn test_match_char_literal_pattern_invalid_escape_errors() {
    let err = parse_contract("match c { '\\q' => 1, _ => 0 }");
    assert!(
        err.is_err(),
        "expected parse error for invalid escape '\\q', got Ok: {err:?}"
    );
}
