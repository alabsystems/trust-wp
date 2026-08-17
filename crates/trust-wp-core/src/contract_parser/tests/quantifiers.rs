// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::formula::{intern_sort_name, resolve_sort_name};

// --- Basic quantifier tests ---

#[test]
fn test_forall_simple() {
    // forall<x: Int> x >= 0
    let expr = parse_ok("forall<x: Int> x >= 0");
    assert!(matches!(expr, PureExpr::Forall { var, .. } if var == "x"));
}

#[test]
fn test_exists_simple() {
    // exists<x: Int> x > 0
    let expr = parse_ok("exists<x: Int> x > 0");
    assert!(matches!(expr, PureExpr::Exists { var, .. } if var == "x"));
}

#[test]
fn test_forall_with_implication() {
    // forall<i: Int> i >= 0 ==> result@[i] > 0
    let expr = parse_ok("forall<i: Int> i >= 0 ==> x > 0");
    if let PureExpr::Forall {
        ref var, ref body, ..
    } = expr
    {
        assert_eq!(var, "i");
        assert!(matches!(
            body.as_ref(),
            PureExpr::BinOp(_, BinOp::Implies, _)
        ));
    } else {
        panic!("Expected Forall, got {expr:?}");
    }
}

#[test]
fn test_forall_with_and() {
    // forall<i: Int> 0 <= i && i < n
    let expr = parse_ok("forall<i: Int> 0 <= i && i < n");
    if let PureExpr::Forall {
        ref var, ref body, ..
    } = expr
    {
        assert_eq!(var, "i");
        assert!(matches!(body.as_ref(), PureExpr::BinOp(_, BinOp::And, _)));
    } else {
        panic!("Expected Forall, got {expr:?}");
    }
}

#[test]
fn test_nested_quantifiers() {
    // forall<x: Int> exists<y: Int> x <= y
    let expr = parse_ok("forall<x: Int> exists<y: Int> x <= y");
    if let PureExpr::Forall {
        var: ref x_var,
        var_sort: Some(ExprSort::Int),
        body: ref inner,
        ..
    } = expr
    {
        assert_eq!(x_var, "x");
        if let PureExpr::Exists {
            var: y_var,
            var_sort: Some(ExprSort::Int),
            body,
            ..
        } = inner.as_ref()
        {
            assert_eq!(y_var, "y");
            assert!(matches!(body.as_ref(), PureExpr::BinOp(_, BinOp::Le, _)));
        } else {
            panic!("Expected Exists with Int sort, got {inner:?}");
        }
    } else {
        panic!("Expected Forall with Int sort, got {expr:?}");
    }
}

#[test]
fn test_quantifier_error_missing_angle() {
    // forall(x: Int) - wrong syntax (should use < not ()
    let err = parse_contract("forall(x: Int) x > 0").unwrap_err();
    assert!(
        err.message.contains("expected '<'"),
        "expected angle-bracket error, got: {}",
        err.message
    );
}

#[test]
fn test_quantifier_accepts_non_int_type() {
    // Non-Int types are accepted; Bool is mapped to ExprSort::Bool (#968)
    let expr = parse_ok("forall<x: Bool> x");
    assert!(
        matches!(&expr, PureExpr::Forall { var, var_sort: Some(ExprSort::Bool), .. } if var == "x"),
        "Bool type should produce ExprSort::Bool, got {expr:?}"
    );
}

#[test]
fn test_quantifier_sort_preservation_bool() {
    // forall<b: bool> !b — lowercase bool maps to ExprSort::Bool (#968)
    let expr = parse_ok("forall<b: bool> !b");
    assert!(
        matches!(&expr, PureExpr::Forall { var, var_sort: Some(ExprSort::Bool), .. } if var == "b"),
        "bool type should produce ExprSort::Bool, got {expr:?}"
    );
}

#[test]
fn test_quantifier_sort_preservation_int_types() {
    // Various integer types all map to ExprSort::Int (#968)
    for (input, type_name) in [
        ("forall<x: Int> x > 0", "Int"),
        ("forall<x: i32> x > 0", "i32"),
        ("forall<x: u64> x > 0", "u64"),
        ("forall<x: usize> x > 0", "usize"),
    ] {
        let expr = parse_ok(input);
        assert!(
            matches!(
                &expr,
                PureExpr::Forall {
                    var_sort: Some(ExprSort::Int),
                    ..
                }
            ),
            "{type_name} should produce ExprSort::Int, got {expr:?}"
        );
    }
}

#[test]
fn test_quantifier_sort_preservation_seq() {
    // Seq type maps to ExprSort::Seq (#968)
    let expr = parse_contract("forall<s: Seq> s.len() > 0").unwrap();
    assert!(
        matches!(
            &expr,
            PureExpr::Forall {
                var_sort: Some(ExprSort::Seq),
                ..
            }
        ),
        "Seq type should produce ExprSort::Seq, got {expr:?}"
    );
}

#[test]
fn test_quantifier_sort_preservation_vec_generic() {
    // Vec<T> maps to ExprSort::Seq (#968)
    let expr = parse_contract("forall<v: Vec<i32>> v.len() > 0").unwrap();
    assert!(
        matches!(
            &expr,
            PureExpr::Forall {
                var_sort: Some(ExprSort::Seq),
                ..
            }
        ),
        "Vec<T> type should produce ExprSort::Seq, got {expr:?}"
    );
}

#[test]
fn test_quantifier_sort_elided_is_none() {
    // Type-elided variables produce var_sort: None (#968)
    let expr = parse_ok("forall<x> x > 0");
    assert!(
        matches!(&expr, PureExpr::Forall { var_sort: None, .. }),
        "Elided type should produce None, got {expr:?}"
    );
}

#[test]
fn test_quantifier_sort_unknown_type_is_none() {
    // Unknown custom types (non-generic params) produce var_sort: None (#968)
    let expr = parse_ok("exists<r: FooType> true");
    assert!(
        matches!(&expr, PureExpr::Exists { var_sort: None, .. }),
        "Unknown custom type should produce None, got {expr:?}"
    );
}

#[test]
fn test_quantifier_sort_generic_type_param_is_type_param() {
    // Generic type params like T/E produce TypeParam sort (#2062)
    let expr = parse_ok("exists<t: T> true");
    let expected_t = ExprSort::TypeParam(intern_sort_name("T"));
    assert!(
        matches!(
            &expr,
            PureExpr::Exists {
                var_sort: Some(sort),
                ..
            } if *sort == expected_t
        ),
        "Generic type param T should produce TypeParam, got {expr:?}"
    );

    let expr_e = parse_ok("exists<e: E> true");
    let expected_e = ExprSort::TypeParam(intern_sort_name("E"));
    assert!(
        matches!(
            &expr_e,
            PureExpr::Exists {
                var_sort: Some(sort),
                ..
            } if *sort == expected_e
        ),
        "Generic type param E should produce TypeParam, got {expr_e:?}"
    );
}

#[test]
fn test_quantifier_sort_generic_ref_param_is_type_param() {
    // &T should preserve the shared-reference wrapper around the generic sort. (#2141)
    let expr = parse_ok("forall<t: &T> true");
    let expected = ExprSort::Ref(Box::new(ExprSort::TypeParam(intern_sort_name("T"))));
    assert!(
        matches!(
            &expr,
            PureExpr::Forall {
                var_sort: Some(sort),
                ..
            } if *sort == expected
        ),
        "&T should produce TypeParam, got {expr:?}"
    );
}

#[test]
fn test_quantifier_sort_generic_mut_ref_param_is_type_param() {
    // &mut T should preserve the mutable-reference wrapper around the generic sort. (#2141)
    let expr = parse_ok("exists<t: &mut T> true");
    let expected = ExprSort::MutRef(Box::new(ExprSort::TypeParam(intern_sort_name("T"))));
    assert!(
        matches!(
            &expr,
            PureExpr::Exists {
                var_sort: Some(sort),
                ..
            } if *sort == expected
        ),
        "&mut T should produce TypeParam, got {expr:?}"
    );
}

#[test]
fn test_quantifier_sort_hash_map_into_iter_mut_ref() {
    let expr = parse_ok("exists<it1: &mut hash_map::IntoIter<K, V>> true");
    let PureExpr::Exists {
        var_sort: Some(ExprSort::MutRef(inner)),
        ..
    } = expr
    else {
        panic!("expected mutable reference datatype sort, got {expr:?}");
    };

    let ExprSort::Datatype(sort_id) = inner.as_ref() else {
        panic!("expected datatype inner sort, got {inner:?}");
    };
    assert_eq!(
        resolve_sort_name(*sort_id),
        "std::collections::hash_map::IntoIter"
    );
}

#[test]
fn test_quantifier_sort_hash_map_iter_mut_ref() {
    let expr = parse_ok("exists<it1: &mut hash_map::IterMut<K, V>> true");
    let PureExpr::Exists {
        var_sort: Some(ExprSort::MutRef(inner)),
        ..
    } = expr
    else {
        panic!("expected mutable reference datatype sort, got {expr:?}");
    };

    let ExprSort::Datatype(sort_id) = inner.as_ref() else {
        panic!("expected datatype inner sort, got {inner:?}");
    };
    assert_eq!(
        resolve_sort_name(*sort_id),
        "std::collections::hash_map::IterMut"
    );
}

#[test]
fn test_quantifier_sort_hash_set_iter_shared_ref() {
    let expr = parse_ok("forall<it1: &hash_set::Iter<K>> true");
    let PureExpr::Forall {
        var_sort: Some(ExprSort::Ref(inner)),
        ..
    } = expr
    else {
        panic!("expected shared reference datatype sort, got {expr:?}");
    };

    let ExprSort::Datatype(sort_id) = inner.as_ref() else {
        panic!("expected datatype inner sort, got {inner:?}");
    };
    assert_eq!(
        resolve_sort_name(*sort_id),
        "std::collections::hash_set::Iter"
    );
}

#[test]
fn test_quantifier_sort_multi_var_mixed() {
    // Multi-variable quantifier with mixed sorts (#968)
    // forall<x: i32, b: bool> body → nested Forall with per-variable sorts
    let expr = parse_ok("forall<x: i32, b: bool> x > 0 ==> b");
    if let PureExpr::Forall {
        var: ref x_var,
        var_sort: Some(ExprSort::Int),
        body: ref inner,
        ..
    } = expr
    {
        assert_eq!(x_var, "x");
        assert!(
            matches!(&**inner, PureExpr::Forall { var, var_sort: Some(ExprSort::Bool), .. } if var == "b"),
            "Inner var should have Bool sort, got {inner:?}"
        );
    } else {
        panic!("Expected Forall with Int sort, got {expr:?}");
    }
}

// Trigger annotation tests (Part of #228)

#[test]
fn test_forall_single_trigger() {
    // forall<x: Int> #[trigger(f(x))] x >= 0 ==> g(x) > 0
    let expr = parse_contract("forall<x: Int> #[trigger(f(x))] x >= 0 ==> g(x) > 0").unwrap();
    if let PureExpr::Forall {
        ref var,
        var_sort: _,
        ref body,
        ref triggers,
    } = expr
    {
        assert_eq!(var, "x");
        assert_eq!(triggers.len(), 1);
        assert_eq!(triggers[0].len(), 1);
        // Check trigger is f(x)
        if let PureExpr::MethodCall {
            receiver, method, ..
        } = &triggers[0][0]
        {
            // f(x) parses as x.f() due to method call syntax
            assert!(matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "f"));
            assert!(method.is_empty() || method == "x");
        }
        assert!(matches!(
            body.as_ref(),
            PureExpr::BinOp(_, BinOp::Implies, _)
        ));
    } else {
        panic!("Expected Forall, got {expr:?}");
    }
}

#[test]
fn test_forall_trigger_with_boolean_ops() {
    // Allow full expressions in triggers
    let expr = parse_contract("forall<x: Int> #[trigger(x > 0 && x < 10)] x >= 0").unwrap();
    if let PureExpr::Forall { ref triggers, .. } = expr {
        assert_eq!(triggers.len(), 1);
        assert_eq!(triggers[0].len(), 1);
        assert!(matches!(triggers[0][0], PureExpr::BinOp(_, BinOp::And, _)));
    } else {
        panic!("Expected Forall, got {expr:?}");
    }
}

#[test]
fn test_forall_multi_trigger() {
    // Multi-trigger: both f(x) and g(x) must match for instantiation
    let expr = parse_contract("forall<x: Int> #[trigger(f(x), g(x))] x >= 0").unwrap();
    if let PureExpr::Forall { ref triggers, .. } = expr {
        assert_eq!(triggers.len(), 1);
        assert_eq!(triggers[0].len(), 2, "multi-trigger should have 2 exprs");
    } else {
        panic!("Expected Forall, got {expr:?}");
    }
}

#[test]
fn test_forall_multiple_trigger_groups() {
    // Multiple trigger groups: alternative patterns
    let expr = parse_contract("forall<x: Int> #[trigger(f(x))] #[trigger(g(x))] x >= 0").unwrap();
    if let PureExpr::Forall { ref triggers, .. } = expr {
        assert_eq!(triggers.len(), 2, "should have 2 trigger groups");
        assert_eq!(triggers[0].len(), 1);
        assert_eq!(triggers[1].len(), 1);
    } else {
        panic!("Expected Forall, got {expr:?}");
    }
}

#[test]
fn test_exists_with_trigger() {
    let expr = parse_contract("exists<x: Int> #[trigger(h(x))] x > 0 && p(x)").unwrap();
    if let PureExpr::Exists { ref triggers, .. } = expr {
        assert_eq!(triggers.len(), 1);
        assert_eq!(triggers[0].len(), 1);
    } else {
        panic!("Expected Exists, got {expr:?}");
    }
}

#[test]
fn test_forall_no_trigger() {
    // Ensure backwards compatibility - no trigger means empty vec
    let expr = parse_ok("forall<x: Int> x > 0");
    if let PureExpr::Forall { ref triggers, .. } = expr {
        assert!(triggers.is_empty());
    } else {
        panic!("Expected Forall, got {expr:?}");
    }
}

#[test]
fn test_trigger_empty_error() {
    // #[trigger()] is invalid - must have at least one expression
    let err = parse_contract("forall<x: Int> #[trigger()] x > 0").unwrap_err();
    assert!(
        err.message.contains("at least one expression"),
        "expected trigger-empty error, got: {}",
        err.message
    );
}

// Edge case tests for type annotation parsing (Part of #257)

#[test]
fn test_quantifier_type_annotation_space_before_colon() {
    // Space before colon should work (parser uses skip_whitespace)
    let expr = parse_ok("forall<x : Int> x >= 0");
    assert!(matches!(expr, PureExpr::Forall { var, .. } if var == "x"));

    let expr = parse_ok("exists<y : Int> y > 0");
    assert!(matches!(expr, PureExpr::Exists { var, .. } if var == "y"));
}

#[test]
fn test_quantifier_type_annotation_trailing_space() {
    // Trailing space in type should work (parser uses skip_whitespace after type)
    let expr = parse_ok("forall<x: Int > x >= 0");
    assert!(matches!(expr, PureExpr::Forall { var, .. } if var == "x"));
}

#[test]
fn test_quantifier_type_annotation_missing_type() {
    // Missing type after colon - should fail
    let err = parse_contract("forall<x:> x > 0").unwrap_err();
    assert!(
        err.message.contains("expected type name"),
        "expected missing-type error, got: {}",
        err.message
    );
}

#[test]
fn test_quantifier_type_annotation_double_colon() {
    // Double colon (path separator) - should fail (we expect simple type, not path)
    // The parser reads ":" then expects identifier, finds ":" which isn't a valid type
    let err = parse_contract("forall<x::Int> x > 0").unwrap_err();
    assert!(
        err.message.contains("expected type name"),
        "expected type-name error, got: {}",
        err.message
    );
}

#[test]
fn test_quantifier_missing_separator() {
    // Missing comma or colon between var and type — should fail
    let err = parse_contract("forall<x Int> x > 0").unwrap_err();
    assert!(
        err.message.contains("expected '>'"),
        "expected separator error, got: {}",
        err.message
    );
}

#[test]
fn test_quantifier_missing_variable() {
    // Missing variable name - should fail
    let err = parse_contract("forall<: Int> x > 0").unwrap_err();
    assert!(
        err.message.contains("expected variable name"),
        "expected missing-variable error, got: {}",
        err.message
    );
}

// --- Implication tests ---

#[test]
fn test_parse_implies_simple() {
    // p ==> q
    let expr = parse_ok("p ==> q");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Implies, r)
        if matches!(l.as_ref(), PureExpr::Var(lv, _) if lv == "p")
        && matches!(r.as_ref(), PureExpr::Var(rv, _) if rv == "q")
    ));
}

#[test]
fn test_parse_implies_comparison() {
    // x > 0 ==> y > 0
    let expr = parse_ok("x > 0 ==> y > 0");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Implies, r)
        if matches!(l.as_ref(), PureExpr::BinOp(_, BinOp::Gt, _))
        && matches!(r.as_ref(), PureExpr::BinOp(_, BinOp::Gt, _))
    ));
}

#[test]
fn test_parse_implies_right_associative() {
    // a ==> b ==> c should parse as a ==> (b ==> c)
    let expr = parse_ok("a ==> b ==> c");
    if let PureExpr::BinOp(_, BinOp::Implies, right) = &expr {
        assert!(matches!(**right, PureExpr::BinOp(_, BinOp::Implies, _)));
    } else {
        panic!("Expected outer Implies, got {expr:?}");
    }
}

#[test]
fn test_parse_implies_lower_than_or() {
    // p || q ==> r should parse as (p || q) ==> r
    let expr = parse_ok("p || q ==> r");
    if let PureExpr::BinOp(left, BinOp::Implies, _) = &expr {
        assert!(matches!(**left, PureExpr::BinOp(_, BinOp::Or, _)));
    } else {
        panic!("Expected Implies with Or on left, got {expr:?}");
    }
}

#[test]
fn test_parse_implies_lower_than_and() {
    // p && q ==> r should parse as (p && q) ==> r
    let expr = parse_ok("p && q ==> r");
    if let PureExpr::BinOp(left, BinOp::Implies, _) = &expr {
        assert!(matches!(**left, PureExpr::BinOp(_, BinOp::And, _)));
    } else {
        panic!("Expected Implies with And on left, got {expr:?}");
    }
}

#[test]
fn test_parse_implies_with_quantifier_body() {
    // 0 <= i && i < len ==> result@.index_logic(i) == default
    // This is the typical quantifier body pattern
    let expr = parse_ok("0 <= i && i < len ==> result == default");
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Implies, _)));
}

#[test]
fn test_spanned_implies() {
    // Verify spanned parsing for implication
    let spanned = parse_spanned_ok("p ==> q");
    assert!(matches!(
        spanned.expr,
        PureExpr::BinOp(_, BinOp::Implies, _)
    ));
    let span = spanned.span.unwrap();
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 7); // "p ==> q" is 7 chars
}

// --- Extended quantifier tests ---

#[test]
fn test_parse_quantifier_type_elided() {
    // forall<x> x > 0 — no type annotation (Creusot allows this)
    let expr = parse_ok("forall<x> x > 0");
    assert!(matches!(
        &expr,
        PureExpr::Forall { var, .. } if var == "x"
    ));
}

#[test]
fn test_parse_quantifier_type_u32() {
    // forall<x: u32> true — non-Int type accepted
    let expr = parse_ok("forall<x: u32> true");
    assert!(matches!(
        &expr,
        PureExpr::Forall { var, .. } if var == "x"
    ));
}

#[test]
fn test_parse_quantifier_type_generic() {
    // exists<r: F> resolve(r) — generic type variable
    let expr = parse_contract("exists<r: F> resolve(r)").unwrap();
    assert!(matches!(
        &expr,
        PureExpr::Exists { var, .. } if var == "r"
    ));
}

#[test]
fn test_parse_quantifier_type_mut_ref() {
    // exists<r: &mut T> result == r — reference type
    let expr = parse_ok("exists<r: &mut T> result == r");
    assert!(matches!(
        &expr,
        PureExpr::Exists {
            var,
            var_sort: Some(ExprSort::MutRef(_)),
            ..
        } if var == "r"
    ));
}

#[test]
fn test_parse_quantifier_multi_var() {
    // forall<a, b> a + b == b + a — multiple variables, types elided
    let expr = parse_ok("forall<a, b> a + b == b + a");
    // Should nest: Forall { var: "a", body: Forall { var: "b", body: ... } }
    if let PureExpr::Forall {
        var,
        var_sort: _,
        body,
        ..
    } = &expr
    {
        assert_eq!(var, "a");
        assert!(matches!(&**body, PureExpr::Forall { var, .. } if var == "b"));
    } else {
        panic!("Expected nested Forall, got {expr:?}");
    }
}

#[test]
fn test_parse_quantifier_multi_var_typed() {
    // exists<s1: F, r: T> f.postcondition_mut(a, s1, r) — multi-var with types
    let expr = parse_contract("exists<s1: F, r: T> f.postcondition_mut(a, s1, r)").unwrap();
    if let PureExpr::Exists {
        var,
        var_sort: _,
        body,
        ..
    } = &expr
    {
        assert_eq!(var, "s1");
        assert!(matches!(&**body, PureExpr::Exists { var, .. } if var == "r"));
    } else {
        panic!("Expected nested Exists, got {expr:?}");
    }
}

#[test]
fn test_parse_quantifier_three_vars() {
    // exists<st1, st2, r> true — three variables
    let expr = parse_ok("exists<st1, st2, r> true");
    if let PureExpr::Exists {
        var,
        var_sort: _,
        body,
        ..
    } = &expr
    {
        assert_eq!(var, "st1");
        if let PureExpr::Exists {
            var,
            var_sort: _,
            body,
            ..
        } = &**body
        {
            assert_eq!(var, "st2");
            assert!(matches!(&**body, PureExpr::Exists { var, .. } if var == "r"));
        } else {
            panic!("Expected second Exists, got {body:?}");
        }
    } else {
        panic!("Expected outer Exists, got {expr:?}");
    }
}

#[test]
fn test_parse_quantifier_ref_type() {
    // exists<r: &T> true — shared reference type
    let expr = parse_ok("exists<r: &T> true");
    assert!(matches!(
        &expr,
        PureExpr::Exists {
            var,
            var_sort: Some(ExprSort::Ref(_)),
            ..
        } if var == "r"
    ));
}

#[test]
fn test_parse_quantifier_unit_type() {
    // forall<_x: ()> expr — unit type in quantifier binding (#613)
    let expr = parse_contract("forall<_x: ()> true").unwrap();
    assert!(matches!(
        &expr,
        PureExpr::Forall { var, .. } if var == "_x"
    ));
}

#[test]
fn test_parse_quantifier_tuple_type() {
    // exists<p: (i32, i32)> expr — tuple type in quantifier binding (#613)
    let expr = parse_contract("exists<p: (i32, i32)> true").unwrap();
    assert!(matches!(
        &expr,
        PureExpr::Exists { var, .. } if var == "p"
    ));
}

#[test]
fn test_parse_quantifier_spanned() {
    let input = "forall<a, b> a == b";
    let regular = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(regular, spanned.expr);
}
