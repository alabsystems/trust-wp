// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

#[test]
fn test_parse_integer() {
    assert_eq!(parse_ok("42"), PureExpr::Int(42));
    assert_eq!(parse_ok("-42"), PureExpr::Int(-42));
    assert_eq!(parse_ok("0"), PureExpr::Int(0));
}

#[test]
fn test_parse_integer_boundary_values() {
    // i64::MAX should parse successfully
    assert_eq!(parse_ok("9223372036854775807"), PureExpr::Int(i64::MAX));
    // i64::MIN should parse successfully
    assert_eq!(parse_ok("-9223372036854775808"), PureExpr::Int(i64::MIN));
}

#[test]
fn test_parse_integer_overflow() {
    // i64::MAX + 1 should fail
    let result = parse_contract("9223372036854775808");
    assert!(
        result.is_err(),
        "overflow should produce error, got Ok({:?})",
        result.as_ref().ok()
    );

    // Very long digit string should fail
    let result = parse_contract("123456789012345678901234567890");
    assert!(
        result.is_err(),
        "30-digit number should produce error, got Ok({:?})",
        result.as_ref().ok()
    );

    // Leading zeros with overflow should fail
    let result = parse_contract("00000000009223372036854775808");
    assert!(
        result.is_err(),
        "overflow with leading zeros should fail, got Ok({:?})",
        result.as_ref().ok()
    );

    // i64::MIN - 1 (negative overflow) should fail
    let result = parse_contract("-9223372036854775809");
    assert!(
        result.is_err(),
        "negative overflow should produce error, got Ok({:?})",
        result.as_ref().ok()
    );
}

#[test]
fn test_parse_integer_overflow_in_expression() {
    // Overflow in comparison context
    let result = parse_contract("9223372036854775808 > 0");
    assert!(
        result.is_err(),
        "overflow in expression should fail, got Ok({:?})",
        result.as_ref().ok()
    );

    // MAX value in expression should succeed
    let result = parse_contract("9223372036854775807 > 0");
    assert!(
        result.is_ok(),
        "i64::MAX in expression should succeed: {:?}",
        result.as_ref().err()
    );
}

#[test]
fn test_parse_bool() {
    assert_eq!(parse_ok("true"), PureExpr::Bool(true));
    assert_eq!(parse_ok("false"), PureExpr::Bool(false));
}

#[test]
fn test_parse_variable() {
    assert_eq!(parse_ok("x"), PureExpr::Var("x".into(), None));
    assert_eq!(parse_ok("result"), PureExpr::Var("result".into(), None));
    assert_eq!(parse_ok("i32::MIN"), PureExpr::Var("i32::MIN".into(), None));
    assert_eq!(parse_ok("old_x"), PureExpr::Var("old_x".into(), None));
    assert_eq!(
        parse_ok("true_value"),
        PureExpr::Var("true_value".into(), None)
    );
}

#[test]
fn test_parse_comparison() {
    let expr = parse_ok("x > 0");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Gt, r)
        if matches!(l.as_ref(), PureExpr::Var(_, _))
        && matches!(r.as_ref(), PureExpr::Int(0))
    ));
}

#[test]
fn test_parse_equality() {
    let expr = parse_ok("result == x + 1");
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Eq, _)));
}

#[test]
fn test_parse_complex() {
    let expr = parse_ok("x > 0 && x < 100");
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::And, _)));
}

#[test]
fn test_parse_chained_comparison_desugars_to_and() {
    let expr = parse_ok("0 <= i < n");
    assert_eq!(
        expr,
        PureExpr::BinOp(
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Int(0)),
                BinOp::Le,
                Arc::new(PureExpr::Var("i".into(), None)),
            )),
            BinOp::And,
            Arc::new(PureExpr::BinOp(
                Arc::new(PureExpr::Var("i".into(), None)),
                BinOp::Lt,
                Arc::new(PureExpr::Var("n".into(), None)),
            )),
        )
    );
}

#[test]
fn test_parse_parentheses() {
    let expr = parse_contract("(x + 1) * 2").unwrap();
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Mul, _)));
}

#[test]
fn test_parse_singleton_tuple_sugar() {
    let expr = parse_contract("(x,)").unwrap();
    assert_eq!(expr, PureExpr::Var("x".into(), None));
}

#[test]
fn test_parse_multi_item_tuple_sugar() {
    let expr = parse_contract("(x, y)").unwrap();
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(2),
            args: vec![
                PureExpr::Var("x".into(), None),
                PureExpr::Var("y".into(), None)
            ],
        }
    );
}

#[test]
fn test_parse_modulo() {
    // Simple modulo: n % 2
    let expr = parse_ok("n % 2");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Mod, r)
        if matches!(l.as_ref(), PureExpr::Var(v, _) if v == "n")
        && matches!(r.as_ref(), PureExpr::Int(2))
    ));
}

#[test]
fn test_parse_modulo_precedence() {
    // Modulo has same precedence as * and /: x + y % 2
    // Should parse as x + (y % 2)
    let expr = parse_ok("x + y % 2");
    if let PureExpr::BinOp(left, BinOp::Add, right) = &expr {
        assert!(matches!(left.as_ref(), PureExpr::Var(v, _) if v == "x"));
        assert!(matches!(
            right.as_ref(),
            PureExpr::BinOp(l, BinOp::Mod, r)
            if matches!(l.as_ref(), PureExpr::Var(v, _) if v == "y")
            && matches!(r.as_ref(), PureExpr::Int(2))
        ));
    } else {
        panic!("Expected Add at top level, got {expr:?}");
    }
}

#[test]
fn test_parse_wrapping_add_mod_spec() {
    // Wrapping arithmetic spec (#692): the mod-based encoding that replaces
    // the existential quantifier approach. This is the actual ensures clause
    // from WRAPPING_ADD in trust-wp-std/src/std/primitives.rs.
    let input =
        "result@ == (self@ + rhs@ - Self::MIN@) % (Self::MAX@ - Self::MIN@ + 1) + Self::MIN@";
    let expr = parse_ok(input);
    // Top level should be Eq
    assert!(
        matches!(expr, PureExpr::BinOp(_, BinOp::Eq, _)),
        "Expected Eq at top level, got {expr:?}"
    );
}

#[test]
fn test_parse_unary_not() {
    let expr = parse_ok("!valid");
    assert!(matches!(expr, PureExpr::UnOp(UnOp::Not, _)));
}

/// Tests negation of comparison - used by `proof_assert` path conditions (#432)
#[test]
fn test_parse_unary_not_comparison() {
    // This is the format generated by proof_assert.rs for else-branch path conditions
    let expr = parse_contract("!(x >= 0)").unwrap();
    if let PureExpr::UnOp(UnOp::Not, inner) = expr {
        assert!(
            matches!(inner.as_ref(), PureExpr::BinOp(_, BinOp::Ge, _)),
            "Expected comparison inside negation, got {inner:?}"
        );
    } else {
        panic!("Expected UnOp(Not, ...), got {expr:?}");
    }
}

#[test]
fn test_parse_result_comparison() {
    let expr = parse_ok("result >= 0");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Ge, r)
        if matches!(l.as_ref(), PureExpr::Var(_, _))
        && matches!(r.as_ref(), PureExpr::Int(0))
    ));
}

#[test]
fn test_parse_old_simple() {
    let expr = parse_contract("old(x)").unwrap();
    assert!(
        matches!(&expr, PureExpr::Old(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "x"))
    );
}

#[test]
fn test_parse_old_complex() {
    let expr = parse_contract("result == old(x) + 1").unwrap();
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Eq, _)));
}

#[test]
fn test_parse_old_nested() {
    let expr = parse_contract("old(x + y)").unwrap();
    assert!(matches!(
        expr,
        PureExpr::Old(inner) if matches!(inner.as_ref(), PureExpr::BinOp(_, BinOp::Add, _))
    ));
}

/// `old` as a match binding name should parse as a variable, not Old keyword. (#967)
#[test]
fn test_parse_old_as_binding_name_in_match() {
    // Pattern: match result { Some(old) => old == self.lookup(arg1), None => false }
    // The `old` after `Some(` is a binding name; the `old` in the body is a variable.
    let expr =
        parse_contract("match result { Some(old) => old == self.lookup(arg1), None => false }")
            .unwrap();
    match &expr {
        PureExpr::Match { arms, .. } => {
            assert_eq!(arms.len(), 2, "expected 2 match arms");
            // First arm body should be `old == self.lookup(arg1)` — `old` is Var, not Old
            match &arms[0].body {
                PureExpr::BinOp(lhs, BinOp::Eq, _) => {
                    assert!(
                        matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "old"),
                        "LHS of == should be Var(\"old\"), got {lhs:?}",
                    );
                }
                other => panic!("expected BinOp(Eq), got {other:?}"),
            }
        }
        other => panic!("expected Match, got {other:?}"),
    }
}

#[test]
fn test_parse_cast_expression_as_noop() {
    let expr = parse_ok("result == p as *const T");
    assert_eq!(
        expr,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("result".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("p".into(), None)),
        )
    );
}

#[test]
fn test_parse_macro_invocation_in_contract() {
    let expr = parse_ok("a@ == seq![0u32, 1u32]");
    assert_eq!(
        expr,
        PureExpr::BinOp(
            Arc::new(PureExpr::View(Arc::new(PureExpr::Var("a".into(), None)))),
            BinOp::Eq,
            Arc::new(PureExpr::LogicFnCall {
                name: "seq".into(),
                args: vec![PureExpr::Int(0), PureExpr::Int(1)],
            }),
        )
    );
}

#[test]
fn test_parse_empty_seq_macro_invocation() {
    let expr = parse_ok("seq![]");
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: "seq".into(),
            args: vec![],
        }
    );
}

// RustHorn/Creusot-style deref and final operators (Part of #13)
#[test]
fn test_parse_deref_simple() {
    // *v (current value of mutable borrow)
    let expr = parse_ok("*v");
    assert!(
        matches!(&expr, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "v"))
    );
}

#[test]
fn test_parse_final_simple() {
    // ^v (final/prophecy value of mutable borrow)
    let expr = parse_ok("^v");
    assert!(
        matches!(&expr, PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "v"))
    );
}

#[test]
fn test_parse_deref_comparison() {
    // *v > 0 (precondition on current value)
    let expr = parse_ok("*v > 0");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Gt, r)
        if matches!(l.as_ref(), PureExpr::Deref(_))
        && matches!(r.as_ref(), PureExpr::Int(0))
    ));
}

#[test]
fn test_parse_final_comparison() {
    // ^v >= 0 (postcondition on final value)
    let expr = parse_ok("^v >= 0");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Ge, r)
        if matches!(l.as_ref(), PureExpr::Final(_))
        && matches!(r.as_ref(), PureExpr::Int(0))
    ));
}

#[test]
fn test_parse_final_equals_old_deref() {
    // ^v == old(*v) + 1 (typical increment postcondition)
    let expr = parse_contract("^v == old(*v) + 1").unwrap();
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Eq, _) if matches!(l.as_ref(), PureExpr::Final(_))
    ));
}

#[test]
fn test_parse_deref_in_old() {
    // old(*v) captures the initial value of the borrow
    let expr = parse_contract("old(*v)").unwrap();
    assert!(matches!(expr, PureExpr::Old(inner) if matches!(inner.as_ref(), PureExpr::Deref(_))));
}

// Quantifier tests (Part of #110)

// --- Integer literal tests ---

#[test]
fn test_parse_integer_with_underscores() {
    // 1_000_000 — Rust-style underscore separators
    assert_eq!(parse_ok("1_000_000"), PureExpr::Int(1_000_000));
}

#[test]
fn test_parse_integer_with_leading_underscore_sep() {
    // 1_0 — minimal underscore usage
    assert_eq!(parse_ok("1_0"), PureExpr::Int(10));
}

#[test]
fn test_parse_integer_with_type_suffix_u32() {
    // 0u32 — unsigned 32-bit suffix (ignored in contract logic)
    assert_eq!(parse_ok("0u32"), PureExpr::Int(0));
}

#[test]
fn test_parse_integer_with_type_suffix_usize() {
    // 12usize — usize suffix
    assert_eq!(parse_ok("12usize"), PureExpr::Int(12));
}

#[test]
fn test_parse_integer_with_type_suffix_i32() {
    // 42i32 — signed 32-bit suffix
    assert_eq!(parse_ok("42i32"), PureExpr::Int(42));
}

#[test]
fn test_parse_integer_with_type_suffix_int() {
    // 1int — Creusot logic-int suffix
    assert_eq!(parse_ok("1int"), PureExpr::Int(1));
}

#[test]
fn test_parse_integer_underscore_and_suffix() {
    // 1_000_000u32 — both underscores and type suffix
    assert_eq!(parse_ok("1_000_000u32"), PureExpr::Int(1_000_000));
}

#[test]
fn test_parse_integer_suffix_in_expression() {
    // x != 0u32 — suffix in comparison context
    let expr = parse_ok("x != 0u32");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Ne, r)
        if matches!(l.as_ref(), PureExpr::Var(_, _))
        && matches!(r.as_ref(), PureExpr::Int(0))
    ));
}

#[test]
fn test_parse_integer_underscore_in_comparison() {
    // a <= 1_000_000u32 — Creusot-style bounded comparison
    let expr = parse_ok("a <= 1_000_000u32");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Le, r)
        if matches!(l.as_ref(), PureExpr::Var(_, _))
        && matches!(r.as_ref(), PureExpr::Int(1_000_000))
    ));
}

#[test]
fn test_parse_integer_suffix_not_consumed_as_identifier() {
    // Ensure `u32var` is not confused with suffix + identifier
    let expr = parse_ok("u32var");
    assert_eq!(expr, PureExpr::Var("u32var".into(), None));
}

#[test]
fn test_parse_integer_suffix_spanned() {
    let input = "42u32";
    let regular = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(regular, spanned.expr);
}

#[test]
fn test_parse_integer_int_suffix_spanned() {
    let input = "1int";
    let regular = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(regular, spanned.expr);
}

// --- Spanned tests ---

#[test]
fn test_spanned_integer() {
    let spanned = parse_spanned_ok("42");
    assert_eq!(spanned.expr, PureExpr::Int(42));
    let span = spanned.span.unwrap();
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 2);
}

#[test]
fn test_spanned_variable() {
    let spanned = parse_spanned_ok("result");
    assert_eq!(spanned.expr, PureExpr::Var("result".into(), None));
    let span = spanned.span.unwrap();
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 6);
}

#[test]
fn test_spanned_comparison() {
    // "x > 0" - full expression spans 0..5
    let spanned = parse_spanned_ok("x > 0");
    let span = spanned.span.unwrap();
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 5);
    assert!(matches!(spanned.expr, PureExpr::BinOp(_, BinOp::Gt, _)));
}

#[test]
fn test_spanned_with_leading_whitespace() {
    // "  42" - span should cover just "42", positions 2..4
    let spanned = parse_spanned_ok("  42");
    let span = spanned.span.unwrap();
    assert_eq!(span.start, 2);
    assert_eq!(span.end, 4);
}

#[test]
fn test_spanned_complex() {
    // "x + y * z" - full expression
    let spanned = parse_spanned_ok("x + y * z");
    let span = spanned.span.unwrap();
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 9);
}

#[test]
fn test_spanned_old() {
    // "old(x)" - full expression including old keyword
    let spanned = parse_contract_spanned("old(x)").unwrap();
    let span = spanned.span.unwrap();
    assert_eq!(span.start, 0);
    assert_eq!(span.end, 6);
    assert!(matches!(spanned.expr, PureExpr::Old(_)));
}

#[test]
fn test_spanned_equivalence() {
    // Verify spanned parsing produces same AST as regular parsing
    let inputs = [
        "x > 0",
        "result == x + 1",
        "x >= 0 && x <= 100",
        "old(x) + 1",
        "*v > 0",
        "^v == old(*v)",
        "!flag || value > 0",
        // View and method call expressions (Part of #110)
        "self@",
        "result@.len()",
        "self@.push_back(v)",
        "(^self)@ == self@.push_back(value)",
        // Implication operator (Part of #110)
        "p ==> q",
        "x > 0 ==> y > 0",
        "p && q ==> r",
        // Edge cases (Part of #136)
        "*(*v)",
        "std::i32::MAX",
        "*v + *w",
        "^v == old(*v) + old(*w)",
        "*(*(*v))",
        "^v - old(*v)",
        "(*self)@.len()",
        "(^self)@.len()",
    ];
    for input in inputs {
        let regular = parse_ok(input);
        let spanned = parse_spanned_ok(input);
        assert_eq!(regular, spanned.expr, "AST mismatch for input: {input}");
    }
}

// --- Reference tests ---

#[test]
fn test_parse_ref_transparent() {
    // &x — reference is transparent in contract logic
    let expr = parse_ok("&x");
    assert_eq!(expr, PureExpr::Var("x".into(), None));
}

#[test]
fn test_parse_mut_ref_transparent() {
    // &mut x — mutable reference is transparent
    let expr = parse_ok("&mut x");
    assert_eq!(expr, PureExpr::Var("x".into(), None));
}

#[test]
fn test_parse_ref_in_equality() {
    // result == &mut r.0 — Creusot-style contract
    let expr = parse_ok("result == &mut r.0");
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Eq, _)));
}

#[test]
fn test_parse_ref_nested_deref() {
    // result == &mut **x — reference of double deref
    let expr = parse_ok("result == &mut **x");
    if let PureExpr::BinOp(_, BinOp::Eq, right) = &expr {
        // &mut is transparent, so right is **x = Deref(Deref(x))
        assert!(matches!(
            right.as_ref(),
            PureExpr::Deref(d1)
            if matches!(d1.as_ref(), PureExpr::Deref(d2)
                if matches!(d2.as_ref(), PureExpr::Var(_, _)))
        ));
    } else {
        panic!("Expected BinOp(Eq), got {expr:?}");
    }
}

#[test]
fn test_parse_logical_and_not_confused_with_ref() {
    // a && b — logical AND should still work, not confused with &&reference
    let expr = parse_ok("a && b");
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::And, _)));
}

#[test]
fn test_parse_ref_spanned() {
    let input = "&mut x";
    let regular = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(regular, spanned.expr);
}

// --- Mixed ampersand tests ---

#[test]
fn test_parse_ref_then_logical_and() {
    // &x && y — `&x` is transparent ref, `&&` is logical AND.
    // Expected: BinOp(Var("x"), And, Var("y"))
    let expr = parse_ok("&x && y");
    if let PureExpr::BinOp(left, BinOp::And, right) = &expr {
        let PureExpr::Var(lhs, _) = left.as_ref() else {
            panic!("Expected Var on left, got {left:?}");
        };
        let PureExpr::Var(rhs, _) = right.as_ref() else {
            panic!("Expected Var on right, got {right:?}");
        };
        assert_eq!(lhs, "x");
        assert_eq!(rhs, "y");
    } else {
        panic!("Expected BinOp(Var(x), And, Var(y)), got {expr:?}");
    }
}

#[test]
fn test_parse_logical_and_then_ref() {
    // x && &y — `&&` is logical AND, `&y` is transparent ref.
    // Expected: BinOp(Var("x"), And, Var("y"))
    let expr = parse_ok("x && &y");
    if let PureExpr::BinOp(left, BinOp::And, right) = &expr {
        let PureExpr::Var(lhs, _) = left.as_ref() else {
            panic!("Expected Var on left, got {left:?}");
        };
        let PureExpr::Var(rhs, _) = right.as_ref() else {
            panic!("Expected Var on right, got {right:?}");
        };
        assert_eq!(lhs, "x");
        assert_eq!(rhs, "y");
    } else {
        panic!("Expected BinOp(Var(x), And, Var(y)), got {expr:?}");
    }
}

#[test]
fn test_parse_bitwise_and_then_logical_and() {
    // x & y && z — bitwise AND binds tighter than logical AND.
    // Expected: BinOp(BinOp(x, BitAnd, y), And, z)
    let expr = parse_ok("x & y && z");
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::And, r)
        if matches!(l.as_ref(), PureExpr::BinOp(ll, BinOp::BitAnd, lr)
            if matches!(ll.as_ref(), PureExpr::Var(_, _))
            && matches!(lr.as_ref(), PureExpr::Var(_, _)))
        && matches!(r.as_ref(), PureExpr::Var(_, _))
    ));
}

#[test]
fn test_parse_mut_ref_then_logical_and() {
    // &mut x && y — `&mut x` is transparent ref, `&&` is logical AND.
    // Expected: BinOp(Var("x"), And, Var("y"))
    let expr = parse_ok("&mut x && y");
    if let PureExpr::BinOp(left, BinOp::And, right) = &expr {
        let PureExpr::Var(lhs, _) = left.as_ref() else {
            panic!("Expected Var on left, got {left:?}");
        };
        let PureExpr::Var(rhs, _) = right.as_ref() else {
            panic!("Expected Var on right, got {right:?}");
        };
        assert_eq!(lhs, "x");
        assert_eq!(rhs, "y");
    } else {
        panic!("Expected BinOp(Var(x), And, Var(y)), got {expr:?}");
    }
}

#[test]
fn test_parse_mixed_ampersand_spanned_equivalence() {
    // Spanned and unspanned parsing should agree for mixed forms.
    let input = "x & y && z";
    let regular = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(regular, spanned.expr);
}
