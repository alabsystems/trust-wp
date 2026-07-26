// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// --- Creusot compatibility tests ---

#[test]
fn test_parse_inc_max_ensures() {
    // From inc_max.rs: if *ma >= *mb { *mb == ^mb && result == ma } else { ... }
    let input = "if *ma >= *mb { *mb == ^mb && result == ma } else { *ma == ^ma && result == mb }";
    let expr = parse_ok(input);
    assert!(matches!(expr, PureExpr::Ite(_, _, _)));
}

#[test]
fn test_parse_mutable_capture_ensures() {
    // From 07_mutable_capture.rs: x@ == old(x@ + 1)
    let input = "x@ == old(x@ + 1)";
    let expr = parse_ok(input);
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Eq, _)));
}

#[test]
fn test_parse_division_requires() {
    // From division.rs: x != 0u32
    let input = "x != 0u32";
    let expr = parse_ok(input);
    assert!(matches!(
        expr,
        PureExpr::BinOp(l, BinOp::Ne, r)
        if matches!(l.as_ref(), PureExpr::Var(_, _))
        && matches!(r.as_ref(), PureExpr::Int(0))
    ));
}

#[test]
fn test_parse_bounded_comparison() {
    // From inc_max.rs: a <= 1_000_000u32
    let input = "a <= 1_000_000u32";
    let expr = parse_ok(input);
    assert!(matches!(
        expr,
        PureExpr::BinOp(_, BinOp::Le, r) if matches!(r.as_ref(), PureExpr::Int(1_000_000))
    ));
}

#[test]
fn test_parse_closure_spec_method() {
    // From 06_fn_specs.rs: f.precondition(a)
    let input = "f.precondition(a)";
    let expr = parse_ok(input);
    assert!(matches!(
        expr,
        PureExpr::MethodCall { ref method, .. } if method == "precondition"
    ));
}

#[test]
fn test_parse_closure_postcondition_with_resolve() {
    // From 06_fn_specs.rs:
    // exists<f2: F> f.postcondition_mut(a, f2, result) && resolve(f2)
    let input = "exists<f2: F> f.postcondition_mut(a, f2, result) && resolve(f2)";
    let expr = parse_ok(input);
    assert!(matches!(&expr, PureExpr::Exists { var, var_sort: _, .. } if var == "f2"));
}

#[test]
fn test_parse_multi_var_quantifier_with_implication() {
    // From 07_mutable_capture.rs:
    // forall<st1, r> f.postcondition_mut((), st1, r) ==> st1.precondition(())
    let input = "forall<st1, r> f.postcondition_mut((), st1, r) ==> st1.precondition(())";
    let expr = parse_ok(input);
    if let PureExpr::Forall {
        var,
        var_sort: _,
        body,
        ..
    } = &expr
    {
        assert_eq!(var, "st1");
        if let PureExpr::Forall {
            var,
            var_sort: _,
            body,
            ..
        } = &**body
        {
            assert_eq!(var, "r");
            assert!(matches!(&**body, PureExpr::BinOp(_, BinOp::Implies, _)));
        } else {
            panic!("Expected inner Forall, got {body:?}");
        }
    } else {
        panic!("Expected outer Forall, got {expr:?}");
    }
}

#[test]
fn test_parse_final_borrows_result() {
    // From final_borrows.rs: result == &mut r.0
    let input = "result == &mut r.0";
    let expr = parse_ok(input);
    if let PureExpr::BinOp(_, BinOp::Eq, right) = &expr {
        // &mut is transparent, r.0 is tuple field access
        assert!(matches!(
            &**right,
            PureExpr::LogicFnCall { ref name, .. } if name.contains("tuple_get")
        ));
    } else {
        panic!("Expected BinOp(Eq), got {expr:?}");
    }
}

#[test]
fn test_parse_v_at_len_with_underscore_lit() {
    // v@.len() == 42 with v@.len() < 1_000_000
    let input = "v@.len() < 1_000_000";
    let expr = parse_ok(input);
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Lt, _)));
}

#[test]
fn test_parse_index_with_ref() {
    // result == &mut v[12] — indexing with reference
    let input = "result == &mut v[12]";
    let expr = parse_ok(input);
    if let PureExpr::BinOp(_, BinOp::Eq, right) = &expr {
        // &mut is transparent, v[12] becomes MethodCall(index_logic)
        assert!(matches!(
            &**right,
            PureExpr::MethodCall { ref method, .. } if method == "index_logic"
        ));
    } else {
        panic!("Expected BinOp(Eq), got {expr:?}");
    }
}

/// Bulk test: all 157 unique contract expressions extracted from the 97
/// Contract strings from the Creusot compat harness "error" set (at commit befa9c5).
/// Tracks parser coverage of real-world Creusot contract syntax.
///
/// Commented-out entries are known unsupported: seq! macro, char literals,
/// closure literals, pointer casts.
const CREUSOT_ERROR_CONTRACTS: &[&str] = &[
    "!b",
    "!x",
    // "'Ã'.to_utf8() == seq![0xC3u8, 0x83u8]",  // char literals + seq! macro — unsupported
    "(*(*x).1)@ == 2",
    "(*(*x.1))@ == 2",
    "(**((*x).1))@ == 3",
    "(**bx)@ == 1 && (***by)@ == 1",
    "(*a)@ <= u64::MAX@ / 2",
    "(*f).postcondition_mut((1i32,), ^f, result)",
    "(*f).precondition((1i32,))",
    "(*t).a@ < 1000",
    "(^*old(bx))@ + (^**old(by))@ == 3",
    // "(^a)@ == seq![0u32, 1u32, 1u32, 0u32]",  // seq! macro — unsupported
    "(^r)@ == 7",
    "(^t)@ == t@.set((*t).a@,1)",
    "(^x.0)@ == 5",
    "(x@ == 1 && exists<y: i32> result == Some(y) && y@ == x@ + 1) || (x@ != 1 && result == None)",
    "*a == 3u64",
    "*result == *(*b).1",
    "*result == *(*x0).1",
    "*result == *(*x1).1",
    "*result == *(*x2).1",
    "*result == **x",
    "*x == ^x",
    "0 <= (*t).a@",
    "Self::f() == ()",
    "^(*b).1 == ^(^b).1",
    "^(*x0).1 == ^(^x0).1",
    "^(*x1).1 == ^(^x1).1",
    "^(*x2).1 == ^(^x2).1",
    "^_x.0 == *_x.0",
    "^_x.1 == *_x.1",
    "^a > *a",
    "^result == *(^b).1",
    "^result == *(^x0).1",
    "^result == *(^x1).1",
    "^result == *(^x2).1",
    "^result == *^x",
    "_a == from_ty(to_ty(_a))",
    "a <= 1_000_000u32 && b <= 1_000_000u32",
    "a <= 1_000_000u32 && b <= 1_000_000u32 && k <= 1_000_000u32",
    "a@ != 0",
    "a@ < 0",
    // "a@ == seq![0u32, 0u32, 0u32, 0u32]",  // seq! macro — unsupported
    "a@ > 0",
    "b@ != 0",
    "b@ != 0 && (a@ != -128 || b@ != -1)",
    "c(x)",
    "c.bar == 2u32",
    // "c@ == |z: u32| z@ % 2 == 0",  // closure literal — unsupported
    "exists<f2: &F, r> *f2 == f && f2.postcondition((), r)",
    "exists<f2: F, r> f2.postcondition_mut((), f2, r)",
    "exists<f2: F> f.postcondition_mut(a, f2, result) && resolve(f2)",
    "exists<f2> f.postcondition_mut((1i32,), f2, result)",
    "exists<f2> f.postcondition_mut((x,), f2, result) && resolve(f2)",
    "exists<r> f.postcondition_once((), r)",
    "exists<st1, st2, r> f.postcondition_mut((), st1, r) && st1.postcondition_mut((), st2, result) && resolve(st2)",
    "f.postcondition((1i32,), result)",
    "f.postcondition((x,), result)",
    "f.postcondition(a, result)",
    "f.postcondition_once((), ())",
    "f.postcondition_once((), result)",
    "f.postcondition_once((1i32,), result)",
    "f.postcondition_once((x,), result)",
    "f.postcondition_once(a, result)",
    "f.precondition(())",
    "f.precondition((0usize,))",
    "f.precondition((1i32,))",
    "f.precondition((x,))",
    "f.precondition(a)",
    "false",
    "forall<i, j, k> FSet::interval(i, j).contains(k) == (i <= k && k < j)",
    "forall<i> result.get(i) == (if 0 <= i && i < self.a@ { 1 } else { 0 })",
    "forall<k: K::DeepModelTy, v: &V> (result@.get(k) == Some(v)) == (xs@.get(k) == Some(*v))",
    "forall<k: K::DeepModelTy, v: &mut V> result@.get(k) == Some(v) ==> xs@.get(k) == Some(*v) && (^xs)@.get(k) == Some(^v)",
    "forall<k: K::DeepModelTy, v: V> (^xs)@.get(k) == Some(v) ==> result@.contains(k) && ^result@[k] == v",
    "forall<k: K::DeepModelTy, v: V> xs@.get(k) == Some(v) ==> result@.contains(k) && *result@[k] == v",
    "forall<s: &[u32]> cell@[*s] == (s@.len() == 2 && s[0]@ % 2 == 0 && s[1]@ % 2 == 1)",
    "forall<st1, r> f.postcondition_mut((), st1, r) ==> st1.precondition(())",
    "forall<xs: FSet<T>, f: Mapping<T, U>, y: U> xs.map(f).contains(y) == exists<x: T> xs.contains(x) && f.get(x) == y",
    "forall<xs: FSet<T>, f: Mapping<T, bool>, x: T> xs.filter(f).contains(x) == (xs.contains(x) && f.get(x))",
    "i@ < a@.len()",
    "if *ma >= *mb { *mb == ^mb && result == ma } else { *ma == ^ma && result == mb }",
    "if b { result == r1 } else { result == r2 }",
    "if take_first { result == p.0 && ^p.1 == *p.1 } else { result == p.1 && ^p.0 == *p.0 }",
    "if toggle { result == a && ^b == *b } else { result == b && ^a == *a }",
    "left@ < 8",
    "match x.0 { None => result == &mut x.1, Some(_) => exists<r: &mut T> result == r && (*x).0 == Some(*r) && (^x).0 == Some(^r) }",
    "p.0@ == 1",
    "p.1@ == 1",
    "resolve(_x)",
    "result == &mut (*x.0).1",
    "result == &mut **x",
    "result == &mut r.0",
    "result == &mut r.0.1",
    "result == &mut v[12]",
    "result == &mut v[12usize]",
    "result == ((*y).deep_model() <= (*x).deep_model())",
    "result == (**x)",
    "result == (x.1, x.0)",
    "result == (x@ <= y@)",
    "result == **b",
    "result == *x",
    "result == 0u32",
    "result == 10u32",
    "result == false",
    "result == if *b { Some(false) } else { None }",
    // "result == p as *const T",  // pointer cast — unsupported
    "result == r",
    "result == self.deep_model().lt_log(o.deep_model())",
    "result == true",
    "result == x",
    "result == x + y % z",
    "result == x.0.1",
    "result.0 == &mut r.0",
    "result.0@ % 2 == 0 && result.1@ % 2 == 1",
    "result.0@ == s@ && result.1@ == Seq::empty()",
    "result.1 == &mut r.1",
    "result@ % 2 == 0",
    "result@ == 2",
    "result@ == 3",
    "result@ == 9",
    "result@ == a@ + b@ || result@ == a@ + b@ - 256",
    "result@ == a@ + b@ || result@ == a@ + b@ - 256 || result@ == a@ + b@ + 256",
    "result@ == a@ - b@ || result@ == a@ - b@ + 256",
    "result@ == a@ - b@ || result@ == a@ - b@ + 256 || result@ == a@ - b@ - 256",
    "result@ == n@ * (n@ + 1) / 2",
    "result@ == x@ + 1",
    "result@ == xs@",
    "result@ == xs@.difference(ys@)",
    "result@ == xs@.intersection(ys@)",
    "result@.len() == 5 && result[0]@ == 0 && result[1]@ == 1 && result[2]@ == 2 && result[3]@ == 3 && result[4]@ == 4",
    // "s@ == seq!['Ã']",  // seq! macro with char — unsupported
    "self.deep_model() == self.deep_model()",
    "simple()",
    "tokens.contains(PERMCELL())",
    "true",
    "uses_simple()",
    "v@.len() == 42",
    "x != 0u32",
    "x == 1i32",
    "x == 2i32",
    "x == x",
    "x >= 0",
    "x(a) == ()",
    "x.0@.len() > 0 && x.0@.len() < usize::MAX@",
    "x.id() != y.id()",
    "x.id() == y.id()",
    "x@ < 1000",
    "x@ < 1_000_000",
    "x@ < u32::MAX@ / 1",
    "x@ == (*x)@",
    "x@ == 100_000",
    "x@ == 3",
    "x@ == old(x)@ + 1",
    "x@ == old(x@ + 1)",
    "x@ == y@",
];

#[test]
fn test_bulk_creusot_error_contracts() {
    let mut pass = 0;
    let mut failures = Vec::new();
    for contract in CREUSOT_ERROR_CONTRACTS {
        match parse_contract(contract) {
            Ok(_) => pass += 1,
            Err(e) => {
                failures.push(format!("{contract}: {e}"));
            }
        }
    }

    eprintln!(
        "Bulk parse: {}/{} passed ({} failed)",
        pass,
        CREUSOT_ERROR_CONTRACTS.len(),
        failures.len()
    );
    for f in &failures {
        eprintln!("  FAIL: {f}");
    }

    assert!(
        failures.is_empty(),
        "{} contract(s) failed to parse:\n{}",
        failures.len(),
        failures.join("\n")
    );
}

// --- Creusot parse regressions ---

#[test]
fn test_bug_1538_forall_unit_type() {
    // bug/1538.rs: `forall<_x: ()> foo.bar == ()`
    // Previously: "parse error at position 25: expected type name in quantifier"
    // Now: parses with ExprSort::Unit, enabling quantifier elimination (#1065)
    let expr = parse_contract("forall<_x: ()> foo.bar == ()").unwrap();
    assert!(
        matches!(&expr, PureExpr::Forall { var, var_sort: Some(ExprSort::Unit), .. } if var == "_x"),
        "Unit type should produce ExprSort::Unit, got {expr:?}"
    );
}

#[test]
fn test_forall_nested_tuple_type() {
    // Ensure nested tuple types in quantifiers parse correctly
    let expr = parse_contract("forall<p: (i32, (u8, u16))> true").unwrap();
    assert!(matches!(&expr, PureExpr::Forall { var, var_sort: _, .. } if var == "p"));
}

#[test]
fn test_forall_trailing_comma_tuple_type() {
    // Singleton tuple type: `(T,)`
    let expr = parse_contract("forall<x: (i32,)> true").unwrap();
    assert!(matches!(&expr, PureExpr::Forall { var, var_sort: _, .. } if var == "x"));
}

#[test]
fn test_multi_binding_with_tuple_types() {
    // Comma inside tuple type must not be confused with binding separator (#613)
    let expr = parse_contract("forall<a: (i32, i32), b: ()> a == b").unwrap();
    // Should produce nested Forall: forall a. forall b. a == b
    match &expr {
        PureExpr::Forall {
            var,
            var_sort: _,
            body,
            ..
        } => {
            assert_eq!(var, "a");
            assert!(
                matches!(&**body, PureExpr::Forall { var, var_sort: Some(ExprSort::Unit), .. } if var == "b"),
                "Inner binding b: () should have ExprSort::Unit, got {body:?}"
            );
        }
        other => panic!("Expected nested Forall, got {other:?}"),
    }
}

#[test]
fn test_bug_1538_spanned_path() {
    // Spanned parser delegates to unspanned for quantifiers — verify same fix applies
    let input = "forall<_x: ()> true";
    let unspanned = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(unspanned, spanned.expr);
}

#[test]
fn test_forall_dyn_trait_type() {
    // unsound_dyn.rs: `forall<x: dyn False> x.falso() == ()` (#657)
    // Previously: "parse error at position 14: expected '>' after type in quantifier"
    let expr = parse_contract("forall<x: dyn False> x.falso() == ()").unwrap();
    assert!(matches!(&expr, PureExpr::Forall { var, var_sort: _, .. } if var == "x"));
}

#[test]
fn test_exists_dyn_trait_type() {
    // Verify `dyn` works in exists bindings too
    let expr = parse_contract("exists<x: dyn MyTrait> x.value() > 0").unwrap();
    assert!(matches!(&expr, PureExpr::Exists { var, var_sort: _, .. } if var == "x"));
}

#[test]
fn test_or_pattern_tuple_match_rejects_int_literal_pattern() {
    // test3.rs: `(0, _, _) | (_, 0, _) | (_, _, 0) => 1` (#658).
    // Pearlite does not support matching integer literals; Creusot rejects
    // this pattern with the same diagnostic. trust-wp matches the rejection.
    let err = parse_contract("match v { (0, _, _) | (_, 0, _) | (_, _, 0) => 1, _ => 0 }")
        .expect_err("integer-literal pattern in match should be rejected");
    assert!(
        err.to_string()
            .contains("Pattern matching literals on Int are unsupported by Pearlite"),
        "expected Pearlite int-literal-pattern diagnostic, got {err}",
    );
}

#[test]
fn test_or_pattern_nested_constructor_rejects_int_literal_pattern() {
    // test4.rs: `Some((Some(0), _)) | Some((_, Some(0))) => 1` (#658).
    // Pearlite rejects matching integer literals at any nesting depth;
    // trust-wp follows suit.
    let err = parse_contract("match v { Some((Some(0), _)) | Some((_, Some(0))) => 1, _ => 0 }")
        .expect_err("nested integer-literal pattern in match should be rejected");
    assert!(
        err.to_string()
            .contains("Pattern matching literals on Int are unsupported by Pearlite"),
        "expected Pearlite int-literal-pattern diagnostic, got {err}",
    );
}

// --- Pearlite transparency ---

#[test]
fn test_pearlite_single_arg_unwrapped() {
    // pearlite!{ x == x } should unwrap to the inner expression, NOT produce
    // a LogicFnCall { "pearlite", [...] } — the latter causes Bool/Int sort
    // mismatch in the encoder when used in logic function bodies.
    let expr = parse_ok("pearlite!{ x == x }");
    assert_eq!(
        expr,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Var("x".into(), None)),
        ),
    );
}

#[test]
fn test_pearlite_parens_unwrapped() {
    // pearlite!(x > 0) — paren form also unwraps
    let expr = parse_contract("pearlite!(x > 0)").unwrap();
    assert_eq!(
        expr,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".into(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
    );
}

#[test]
fn test_pearlite_brackets_unwrapped() {
    // pearlite![true] — bracket form also unwraps
    let expr = parse_ok("pearlite![true]");
    assert_eq!(expr, PureExpr::Bool(true));
}

#[test]
fn test_other_macros_not_unwrapped() {
    // seq![1, 2] should still produce LogicFnCall, not be unwrapped
    let expr = parse_ok("seq![1, 2]");
    assert_eq!(
        expr,
        PureExpr::LogicFnCall {
            name: "seq".into(),
            args: vec![PureExpr::Int(1), PureExpr::Int(2)],
        },
    );
}

#[test]
fn test_spanned_pearlite_matches_unspanned() {
    // Self-audit (#610): spanned parser must also unwrap pearlite!
    for input in ["pearlite!{ x == x }", "pearlite!(x > 0)", "pearlite![true]"] {
        let unspanned = parse_ok(input);
        let spanned = parse_spanned_ok(input);
        assert_eq!(
            unspanned, spanned.expr,
            "spanned/unspanned mismatch for: {input}",
        );
        assert!(
            !matches!(unspanned, PureExpr::LogicFnCall { ref name, .. } if name == "pearlite"),
            "pearlite! should be unwrapped, not a LogicFnCall: {input}",
        );
    }
}

#[test]
fn test_pearlite_block_with_let_and_unsized_quantifier() {
    // Regression for unsized_quant.rs: pearlite! brace bodies may contain
    // let-bindings and quantified trailing expressions.
    let input = "pearlite! { let len = |x: [i32]| x@.len(); forall<x: [i32], y: [i32]> { len[x] + len[y] >= 0 } }";
    let result = parse_contract(input);
    assert!(
        result.is_ok(),
        "pearlite block with let + unsized quantifier should parse: {result:?}"
    );
}
