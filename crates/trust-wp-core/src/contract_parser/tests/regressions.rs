// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::*;

// --- Integration tests ---

#[test]
fn test_vec_bounds_with_quantifier() {
    // Realistic: forall<i: Int> 0 <= i && i < self@.len() ==> self@.index_logic(i) >= 0
    let input = "forall<i: Int> 0 <= i && i < self@.len() ==> self@.index_logic(i) >= 0";
    let expr = parse_ok(input);
    assert!(
        matches!(&expr, PureExpr::Forall { var, var_sort: _, .. } if var == "i"),
        "Expected Forall with var 'i'"
    );
    // Verify spanned produces same AST
    let spanned = parse_spanned_ok(input);
    assert_eq!(
        expr, spanned.expr,
        "parse_contract and parse_contract_spanned should match"
    );
}

#[test]
fn test_push_back_postcondition() {
    // Realistic Vec::push postcondition: (^self)@ == self@.push_back(value)
    let input = "(^self)@ == self@.push_back(value)";
    let expr = parse_ok(input);
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Eq, _)));
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_len_postcondition() {
    // Realistic: (^self)@.len() == self@.len() + 1
    let input = "(^self)@.len() == self@.len() + 1";
    let expr = parse_ok(input);
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Eq, _)));
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_unparenthesized_deref_view_equivalence() {
    let input = "*rc@ == 1";
    let expr = parse_ok(input);
    assert!(matches!(
        &expr,
        PureExpr::BinOp(left, BinOp::Eq, right)
            if matches!(left.as_ref(), PureExpr::View(inner)
                if matches!(inner.as_ref(), PureExpr::Deref(rc)
                    if matches!(rc.as_ref(), PureExpr::Var(name, _) if name == "rc")))
            && matches!(right.as_ref(), PureExpr::Int(1))
    ));
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_unparenthesized_final_view_equivalence() {
    let input = "^x@ == 1";
    let expr = parse_ok(input);
    assert!(matches!(
        &expr,
        PureExpr::BinOp(left, BinOp::Eq, right)
            if matches!(left.as_ref(), PureExpr::View(inner)
                if matches!(inner.as_ref(), PureExpr::Final(x)
                    if matches!(x.as_ref(), PureExpr::Var(name, _) if name == "x")))
            && matches!(right.as_ref(), PureExpr::Int(1))
    ));
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_index_valid_precondition() {
    // Realistic: index < self@.len()
    let input = "index < self@.len()";
    let expr = parse_ok(input);
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Lt, _)));
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_swap_postcondition() {
    // Realistic swap postcondition
    let input = "(^a)@ == old(*b) && (^b)@ == old(*a)";
    let expr = parse_ok(input);
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::And, _)));
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_binary_search_precondition() {
    // Realistic sorted precondition with nested quantifiers
    let input = "forall<i: Int> forall<j: Int> 0 <= i && i < j && j < arr@.len() ==> arr@.index_logic(i) <= arr@.index_logic(j)";
    let expr = parse_ok(input);
    assert!(
        matches!(&expr, PureExpr::Forall { var, var_sort: _, .. } if var == "i"),
        "Expected outer Forall with var 'i'"
    );
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_option_match_postcondition() {
    // Realistic Option handling
    let input = "match result { Some(v) => v == x + 1, None => false }";
    let expr = parse_ok(input);
    assert!(matches!(expr, PureExpr::Match { .. }));
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_logic_fn_in_quantifier() {
    // Logic function call inside quantifier
    let input = "forall<x: Int> x >= 0 ==> abs(x) == x";
    let expr = parse_ok(input);
    assert!(matches!(expr, PureExpr::Forall { .. }));
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_existential_element() {
    // Exists with method call
    let input = "exists<i: Int> 0 <= i && i < self@.len() && self@.index_logic(i) == target";
    let expr = parse_ok(input);
    assert!(
        matches!(&expr, PureExpr::Exists { var, var_sort: _, .. } if var == "i"),
        "Expected Exists with var 'i'"
    );
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_mutable_ref_invariant() {
    // Mutable reference contract: ^v == old(*v) + 1
    let input = "^v == old(*v) + 1";
    let expr = parse_ok(input);
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Eq, _)));
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_complex_arithmetic_contract() {
    // Complex arithmetic with parentheses
    let input = "(a + b) * c == a * c + b * c";
    let expr = parse_ok(input);
    assert!(matches!(expr, PureExpr::BinOp(_, BinOp::Eq, _)));
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_chained_comparison_equivalence() {
    let input = "0 <= i < n";
    let expr = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_cast_equivalence() {
    let input = "result == p as *const T";
    let expr = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_macro_invocation_equivalence() {
    let input = "a@ == seq![0u32, 1u32]";
    let expr = parse_ok(input);
    let spanned = parse_spanned_ok(input);
    assert_eq!(expr, spanned.expr);
}

#[test]
fn test_spanned_preserves_positions() {
    // Verify span positions are correct for complex input
    let input = "forall<x: Int> x > 0";
    let spanned = parse_spanned_ok(input);
    let span = spanned.span.unwrap();
    assert_eq!(span.start, 0, "Start should be at beginning");
    assert_eq!(span.end, input.len(), "End should be at end of input");
}

#[test]
fn test_both_apis_error_consistently() {
    // Both APIs should produce equivalent errors for invalid syntax
    let input = "forall x > 0"; // Missing angle brackets
    let err1 = parse_contract(input).unwrap_err();
    let err2 = parse_contract_spanned(input).unwrap_err();
    assert_eq!(err1.message, err2.message, "Error messages should match");
    assert_eq!(err1.position, err2.position, "Error positions should match");
}

// --- Regression tests ---

// ============================================================================
// Wrapping arithmetic spec parsing (#692)
// ============================================================================

/// Verify the modular wrapping arithmetic spec string parses correctly.
///
/// The spec: `result@ == (self@ + rhs@ - Self::MIN@) % (Self::MAX@ - Self::MIN@ + 1) + Self::MIN@`
/// must parse as `Eq(View(result), Add(Mod(Sub(Add(View(self), View(rhs)), View(Self::MIN)), Add(Sub(View(Self::MAX), View(Self::MIN)), 1)), View(Self::MIN)))`.
///
/// Previously, wrapping specs used `exists k: Int :: ...` which silently failed
/// to parse (parser only supports `exists<k: Int>` syntax). The modular encoding
/// uses only standard arithmetic operators that the parser already supports.
#[test]
fn test_parse_wrapping_add_modular_spec() {
    let input =
        "result@ == (self@ + rhs@ - Self::MIN@) % (Self::MAX@ - Self::MIN@ + 1) + Self::MIN@";
    let result = parse_contract(input);
    assert!(
        result.is_ok(),
        "wrapping_add modular spec should parse: {result:?}"
    );

    // Verify the top-level structure: result@ == <expr>
    let expr = result.unwrap();
    if let PureExpr::BinOp(left, BinOp::Eq, _) = &expr {
        let PureExpr::View(view_inner) = left.as_ref() else {
            panic!("expected result@ == <expr>, got: {expr:?}");
        };
        let PureExpr::Var(lhs, _) = view_inner.as_ref() else {
            panic!("expected result@ == <expr>, got: {expr:?}");
        };
        assert_eq!(lhs, "result", "LHS should be result@");
    } else {
        panic!("expected result@ == <expr>, got: {expr:?}");
    }
}

/// Verify all three wrapping spec variants parse.
#[test]
fn test_parse_wrapping_sub_mul_modular_specs() {
    let specs = [
        "result@ == (self@ - rhs@ - Self::MIN@) % (Self::MAX@ - Self::MIN@ + 1) + Self::MIN@",
        "result@ == (self@ * rhs@ - Self::MIN@) % (Self::MAX@ - Self::MIN@ + 1) + Self::MIN@",
    ];
    for spec in &specs {
        let result = parse_contract(spec);
        assert!(
            result.is_ok(),
            "wrapping spec should parse: {spec}\nerror: {result:?}"
        );
    }
}

/// Negative test: the old `exists k: Int :: body` syntax should fail to parse.
///
/// This documents the parser limitation that motivated the modular rewrite (#692).
/// If someone adds support for this syntax later, this test should be updated.
#[test]
fn test_parse_old_existential_syntax_fails() {
    let input = "exists k: Int :: result@ == self@ + rhs@ + k * 256";
    let result = parse_contract(input);
    assert!(
        result.is_err(),
        "old `exists k: Int :: body` syntax should not parse (only exists<k: Int> is supported)"
    );
}

// --- Fully-qualified associated type/const path tests (#985) ---

#[test]
fn test_parse_qualified_path_simple() {
    // <T as Nat>::VALUE
    let result = parse_ok("<T as Nat>::VALUE");
    assert_eq!(result, PureExpr::Var("<T as Nat>::VALUE".to_string(), None));
}

#[test]
fn test_parse_qualified_path_with_generic() {
    // <I3<T> as Nat>::VALUE
    let result = parse_ok("<I3<T> as Nat>::VALUE");
    assert_eq!(
        result,
        PureExpr::Var("<I3<T> as Nat>::VALUE".to_string(), None)
    );
}

#[test]
fn test_parse_qualified_path_with_view() {
    // <I3<T> as Nat>::VALUE@ == T::VALUE@ + T::VALUE@
    let result = parse_contract("<I3<T> as Nat>::VALUE@");
    assert!(
        result.is_ok(),
        "qualified path with view operator should parse: {result:?}"
    );
    // The outer structure should be View(Var(...))
    let expr = result.unwrap();
    assert_eq!(
        expr,
        PureExpr::View(Arc::new(PureExpr::Var(
            "<I3<T> as Nat>::VALUE".to_string(),
            None
        )))
    );
}

#[test]
fn test_parse_qualified_path_in_expression() {
    // <I3<T> as Nat>::VALUE@ == T::VALUE@ + T::VALUE@
    let result = parse_contract("<I3<T> as Nat>::VALUE@ == T::VALUE@ + T::VALUE@");
    assert!(
        result.is_ok(),
        "qualified path in expression should parse: {result:?}"
    );
}

#[test]
fn test_parse_qualified_path_std_trait() {
    // <T as ::std::mem::SizedTypeProperties>::IS_ZST
    // Note: `::std` has leading `::` which the parser should handle within the angle brackets
    let result = parse_contract("result == <T as Trait>::CONST");
    assert!(
        result.is_ok(),
        "qualified path as RHS of comparison should parse: {result:?}"
    );
}

/// Canonicalization must preserve exactly one space between the `as` keyword
/// and a following absolute path (`::std::...`). Stripping that space would
/// produce `<T as::std::...>`, which diverges from the form emitted by the
/// MIR-extract layer and yields two distinct SMT identifiers for the same
/// logical constant. (Wave 7B / #1996)
#[test]
fn test_parse_qualified_path_preserves_space_after_as_before_absolute_path() {
    let result = parse_ok("<T as ::std::mem::SizedTypeProperties>::IS_ZST");
    assert_eq!(
        result,
        PureExpr::Var(
            "<T as ::std::mem::SizedTypeProperties>::IS_ZST".to_string(),
            None
        ),
        "absolute-trait-path canonicalization must keep `as ::`"
    );
}

/// Whitespace variants of the same qualified path must canonicalize to the
/// same string so they reuse a single SMT identifier. (Wave 7B / #1996)
#[test]
fn test_parse_qualified_path_canonicalizes_whitespace_variants() {
    let with_space = parse_ok("<T as ::std::mem::SizedTypeProperties>::IS_ZST");
    let extra_space = parse_ok("<  T   as   ::std::mem::SizedTypeProperties  >::IS_ZST");
    assert_eq!(
        with_space, extra_space,
        "whitespace variants must canonicalize to the same identifier"
    );
}

#[test]
fn test_parse_qualified_path_does_not_break_comparison() {
    // `a < b` should still parse as a comparison, not a qualified path
    let result = parse_ok("a < b");
    assert_eq!(
        result,
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("a".to_string(), None)),
            BinOp::Lt,
            Arc::new(PureExpr::Var("b".to_string(), None))
        )
    );
}

#[test]
fn test_parse_qualified_path_does_not_break_generics() {
    // `forall<x: Int> x > 0` should still parse as a quantifier
    let result = parse_contract("forall<x: Int> x > 0");
    assert!(
        result.is_ok(),
        "quantifier should not be confused with qualified path: {result:?}"
    );
}

// --- Closure expression tests (#985) ---

#[test]
fn test_parse_closure_simple() {
    // |x: Int| x + 1
    let result = parse_contract("|x: Int| x + 1");
    assert!(
        result.is_ok(),
        "simple closure should parse: {:?}",
        result.as_ref().err()
    );
    let expr = result.unwrap();
    assert!(
        matches!(expr, PureExpr::Closure { ref params, .. } if params.len() == 1),
        "should parse as closure with 1 param: {expr:?}"
    );
}

#[test]
fn test_parse_closure_with_slice_type() {
    // |x: [i32]| x@.len() — the pattern from unsized_quant.rs
    let result = parse_contract("|x: [i32]| x@.len()");
    assert!(
        result.is_ok(),
        "closure with slice type param should parse: {result:?}"
    );
    let expr = result.unwrap();
    if let PureExpr::Closure { params, .. } = &expr {
        assert_eq!(params.len(), 1);
        assert_eq!(params[0].0, "x");
        assert_eq!(params[0].1, Some(ExprSort::Seq));
    } else {
        panic!("expected Closure, got {expr:?}");
    }
}

#[test]
fn test_parse_closure_no_params() {
    // || true
    let result = parse_contract("|| true");
    assert!(
        result.is_ok(),
        "zero-param closure should parse: {result:?}"
    );
    let expr = result.unwrap();
    if let PureExpr::Closure { params, body } = &expr {
        assert!(params.is_empty());
        assert_eq!(**body, PureExpr::Bool(true));
    } else {
        panic!("expected Closure, got {expr:?}");
    }
}

#[test]
fn test_parse_closure_in_let_binding() {
    // Closures in pearlite blocks are parsed within `{ ... }` block syntax.
    // `pearlite! { let len = |x: [i32]| x@.len(); len }` becomes block body.
    let result = parse_contract("{ let len = |x: [i32]| x@.len(); len }");
    assert!(
        result.is_ok(),
        "closure in let binding should parse: {result:?}"
    );
}

#[test]
fn test_parse_closure_does_not_break_bitwise_or() {
    // `a || b` should still parse as logical OR, not a closure
    let result = parse_ok("a || b");
    assert!(
        matches!(result, PureExpr::BinOp(_, BinOp::Or, _)),
        "|| should parse as logical OR: {result:?}"
    );
}

// --- Multiline match + trailing-comma tuple tests (#985 result/own) ---

#[test]
fn test_parse_multiline_match() {
    // Multiline match expression with newline between scrutinee and body
    let input =
        "match (self, result)\n{\n(OwnResult::Ok(s), OwnResult::Ok(r)) => true,\n_ => false\n}";
    let result = parse_contract(input);
    assert!(
        result.is_ok(),
        "multiline match should parse: {:?}",
        result.as_ref().err()
    );
    let expr = result.unwrap();
    assert!(
        matches!(expr, PureExpr::Match { ref arms, .. } if arms.len() == 2),
        "expected Match with 2 arms, got: {expr:?}"
    );
}

#[test]
fn test_parse_trailing_comma_tuple_in_match_arm() {
    // T::clone.postcondition((s,), r) — trailing comma tuple as function arg
    let input = "match x { Some(s) => T::clone.postcondition((s,), r), _ => false }";
    let result = parse_contract(input);
    assert!(
        result.is_ok(),
        "match arm with trailing-comma tuple should parse: {result:?}"
    );
}

#[test]
fn test_parse_qualified_default_postcondition_method_call() {
    let input = "T::default.postcondition((), result.0)";
    let result = parse_contract(input);
    assert!(
        result.is_ok(),
        "typed default postcondition method call should parse: {result:?}"
    );
}

#[test]
fn test_parse_result_own_ensures_clause() {
    // Exact ensures clause from result/own Creusot test (multiline with postcondition)
    let input = "match (self, result)\n{\n(OwnResult::Ok(s), OwnResult::Ok(r)) => T::clone.postcondition((s,), r),\n(OwnResult::Err(s), OwnResult::Err(r)) => s == r, _ => false\n}";
    let result = parse_contract(input);
    assert!(
        result.is_ok(),
        "result/own ensures clause should parse: {result:?}"
    );
}

// --- Qualified path function call tests (#352) ---

#[test]
fn test_parse_qualified_path_call_no_args() {
    // `< Self as Foo > :: f()` — tokenstream-serialized qualified path call
    let input = "< Self as Foo > :: f()";
    let result = parse_contract(input).expect("qualified path call should parse");
    assert!(
        matches!(result, PureExpr::LogicFnCall { ref name, ref args }
            if name == "<Self as Foo>::f" && args.is_empty()),
        "qualified path call should be canonicalized: {result:?}"
    );
}

#[test]
fn test_parse_qualified_path_call_with_args() {
    // `< Self as Bar > :: g(x, y)` — qualified path call with arguments
    let input = "< Self as Bar > :: g(x, y)";
    let result = parse_contract(input);
    assert!(
        result.is_ok(),
        "qualified path call with args should parse: {result:?}"
    );
}

#[test]
fn test_parse_qualified_path_no_call() {
    // `< T as Trait > :: VALUE` — qualified path without function call (constant)
    let input = "< T as Trait > :: VALUE";
    let result = parse_contract(input);
    assert!(
        result.is_ok(),
        "qualified path constant should parse: {result:?}"
    );
}

// =============================================================================
// parse_contract_body tests (multi-statement proof_assert! blocks)
// =============================================================================

#[test]
fn test_parse_body_single_expr() {
    // Single expression should work identically to parse_contract
    let result = parse_body_ok("x > 0");
    assert_eq!(result, parse_ok("x > 0"));
}

#[test]
fn test_parse_body_stmt_then_expr() {
    // `lemma_call(); assertion` — leading statement discarded, trailing expr returned
    let result = parse_contract_body("lemma_call(); x > 0").unwrap();
    assert_eq!(result, parse_ok("x > 0"));
}

#[test]
fn test_parse_body_multiple_stmts_then_expr() {
    // Multiple leading statements followed by trailing assertion
    let result = parse_contract_body("lemma_a(); lemma_b(); x > 0").unwrap();
    assert_eq!(result, parse_ok("x > 0"));
}

#[test]
fn test_parse_body_stmt_then_true() {
    // Creusot pattern: `tl.lemma_sum_nonneg(); tr.lemma_sum_nonneg(); true`
    let result = parse_contract_body("tl.lemma_sum_nonneg(); tr.lemma_sum_nonneg(); true").unwrap();
    assert_eq!(result, PureExpr::Bool(true));
}

#[test]
fn test_parse_body_with_leading_exprs_returns_method_calls() {
    let (leading, trailing) = parse_contract_body_with_leading_exprs(
        "tl.lemma_sum_nonneg(); tr.lemma_sum_nonneg(); true",
    )
    .unwrap();
    assert_eq!(trailing, PureExpr::Bool(true));
    assert_eq!(leading.len(), 2);
    assert!(matches!(
        &leading[0],
        PureExpr::MethodCall { method, .. } if method == "lemma_sum_nonneg"
    ));
    assert!(matches!(
        &leading[1],
        PureExpr::MethodCall { method, .. } if method == "lemma_sum_nonneg"
    ));
}

#[test]
fn test_parse_body_trailing_semicolon_yields_unit() {
    // `stmt;` with no trailing expr yields unit
    let result = parse_contract_body("lemma_call();").unwrap();
    assert_eq!(
        result,
        PureExpr::LogicFnCall {
            name: tuple_logic_fn_name(0),
            args: vec![],
        }
    );
}

#[test]
fn test_parse_body_complex_trailing_expr() {
    // Leading lemma + complex trailing expression
    let result = parse_contract_body(
        "lemma_num_of_pos_strictly_increasing(i@, u@); num_of_pos(0, i@ , t@) < num_of_pos(0, i@ + 1, t@)",
    )
    .unwrap();
    // The trailing expression should be a comparison
    match result {
        PureExpr::BinOp(_, BinOp::Lt, _) => {} // expected
        other => panic!("expected comparison, got: {other:?}"),
    }
}

#[test]
fn test_parse_body_with_let_binding() {
    // Let binding followed by expression
    let result = parse_body_ok("let x = 5; x > 0");
    match result {
        PureExpr::Let { var, .. } => assert_eq!(var, "x"),
        other => panic!("expected Let, got: {other:?}"),
    }
}

#[test]
fn test_parse_body_multiline_whitespace() {
    // Multiline input (as would appear in proc macro stringification)
    let input = "lemma_call ()\n;\ntrue";
    let result = parse_body_ok(input);
    assert_eq!(result, PureExpr::Bool(true));
}

/// `proof_assert!(...)` with a `let` binding and trailing assertion in the
/// macro arguments (Creusot multi-statement Pearlite hint). Used in iter
/// reference impls like 04_skip.rs to bind an existential witness:
///
/// ```text
/// proof_assert!(
///     let s = such_that(|s| ...);
///     s.concat(bc) == bc
/// );
/// ```
///
/// The parser must accept this body without erroring. The single arg is
/// either a Let (when the binding is preserved) or the trailing assertion
/// (when leading statements are discarded). Either form is acceptable
/// — proof_assert! is a hint that trust-wp does not act on directly.
#[test]
fn test_proof_assert_macro_with_let_and_trailing_expr() {
    let result = parse_ok("proof_assert!(let s = foo(); s.len() == 0)");
    let PureExpr::LogicFnCall { name, args } = &result else {
        panic!("expected LogicFnCall for proof_assert!, got {result:?}");
    };
    assert_eq!(name, "proof_assert");
    assert_eq!(args.len(), 1, "proof_assert! has one arg (assertion expr)");
    // The arg should be a Let-binding wrapping the trailing assertion.
    let PureExpr::Let { var, body, .. } = &args[0] else {
        panic!("expected Let, got {:?}", args[0]);
    };
    assert_eq!(var, "s");
    assert!(
        matches!(
            body.as_ref(),
            PureExpr::BinOp(_, crate::formula::BinOp::Eq, _)
        ),
        "expected Eq in Let body, got {body:?}"
    );
}

/// `proof_assert!(...)` with multiple leading statements followed by a
/// trailing assertion. All leading lemma-call statements are discarded.
#[test]
fn test_proof_assert_macro_with_multiple_statements() {
    let result = parse_ok("proof_assert!(foo(); bar(); x == y)");
    let PureExpr::LogicFnCall { name, args } = &result else {
        panic!("expected LogicFnCall, got {result:?}");
    };
    assert_eq!(name, "proof_assert");
    assert_eq!(args.len(), 1);
}

/// Backward compatibility: simple single-expression `proof_assert!` still
/// parses correctly after the block-body change.
#[test]
fn test_proof_assert_macro_single_expression() {
    let result = parse_ok("proof_assert!(x == y)");
    let PureExpr::LogicFnCall { name, args } = &result else {
        panic!("expected LogicFnCall, got {result:?}");
    };
    assert_eq!(name, "proof_assert");
    assert_eq!(args.len(), 1);
}
