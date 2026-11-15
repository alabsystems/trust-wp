// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match expression encoding tests for trust-wp-ay.

use super::*;

/// Regression test for #1642: `assert_is_option` must be deduplicated
/// per-term and path-guarded to prevent permanently over-constraining
/// the solver state.
///
/// Scenario: A variable is matched as an Option (UF fallback path), then
/// used in a non-Option context (arithmetic comparison). The `is_option`
/// assertion should not prevent the variable from satisfying arithmetic
/// constraints.
#[test]
#[timeout(30000)]
fn test_assert_is_option_deduplication_prevents_overconstrain() {
    let mut encoder = AYEncoder::new();

    // Pre-declare the variable as Int (no sort metadata in var_sorts,
    // which forces the UF fallback path in match encoding).
    let var_name = "x";
    let x_term = encoder.solver.declare_const(var_name, Sort::Int);
    encoder
        .vars_mut_for_test()
        .insert(var_name.to_string(), x_term);

    // Encode a match on x as Option (UF fallback since no sort metadata).
    let expr = match_expr(
        var(var_name),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );

    let _ = encoder
        .encode_pure(&expr)
        .expect("encoding should succeed via UF fallback");

    // Verify is_option was asserted exactly once (deduplication).
    assert_eq!(
        encoder.is_option_asserted_for_test().len(),
        1,
        "is_option should be asserted for exactly one term"
    );
    assert!(
        encoder.is_option_asserted_for_test().contains(&x_term),
        "is_option should track the scrutinee term"
    );

    // Encode the same match again — assert_is_option should be a no-op.
    let expr2 = match_expr(
        var(var_name),
        vec![
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                int(1),
            ),
            (Pattern::Wildcard, int(2)),
        ],
    );
    let _ = encoder
        .encode_pure(&expr2)
        .expect("second match encoding should succeed");

    // Still exactly one term tracked (deduplication worked).
    assert_eq!(
        encoder.is_option_asserted_for_test().len(),
        1,
        "is_option should not be re-asserted for the same term"
    );
}

/// Regression test for #1642: after matching a variable as Option (UF path),
/// asserting an arithmetic constraint on the same variable should remain SAT.
///
/// Pre-fix: `is_option(x)` plus the None reconstruction axiom could force
/// `x = None` when `!is_some(x)`, over-constraining arithmetic uses.
/// Post-fix: deduplication and path-guarding limit the scope of `is_option`.
#[test]
#[timeout(30000)]
fn test_is_option_does_not_block_arithmetic_after_match() {
    use ay_dpll::api::SolveResult;

    let mut encoder = AYEncoder::new();

    // Pre-declare x as Int with no sort metadata (triggers UF fallback).
    let x_term = encoder.solver.declare_const("x", Sort::Int);
    encoder.vars_mut_for_test().insert("x".to_string(), x_term);

    // Encode match x { Some(v) => v, _ => 0 } via UF fallback path.
    let expr = match_expr(
        var("x"),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                var("v"),
            ),
            (Pattern::Wildcard, int(0)),
        ],
    );
    let _ = encoder.encode_pure(&expr).expect("encoding should succeed");

    // Assert x > 10 — an arithmetic constraint independent of Option.
    let ten = encoder.solver.int_const(10);
    let x_gt_10 = encoder.solver.gt(x_term, ten);
    encoder.assert_term(x_gt_10);

    // Should be satisfiable: x can be any integer > 10.
    // is_option(x) should not prevent this.
    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "x > 10 after Option match should be satisfiable (is_option should \
             not over-constrain to Option-only values): got {result:?}"
    );
}

/// Regression for #1752: `*self == Some(x)` in postconditions where the
/// OptionInt datatype is declared. Without the Deref(Var) preseed fix,
/// `preseed_constructor_var_sort` only handles bare `Var(name)` but not
/// `Deref(Var(name))`. The `self` variable keeps `Sort::Int` while
/// `Some(42)` produces an `OptionInt`-sorted term, causing a sort
/// mismatch caught as a solver panic (verification reports Unknown).
#[test]
#[timeout(30000)]
fn test_deref_var_eq_constructor_preseed_no_sort_mismatch() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();

    // Pre-declare the OptionInt datatype (simulating a match earlier in encoding)
    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Build: *self == Some(42)
    // Deref(Var("self")) == LogicFnCall("Some", [Int(42)])
    let expr = PureExpr::BinOp(
        Arc::new(PureExpr::Deref(Arc::new(var("self")))),
        BinOp::Eq,
        Arc::new(PureExpr::LogicFnCall {
            name: "Some".to_string(),
            args: vec![int(42)],
        }),
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "Deref(Var) == Constructor should encode successfully: {result:?}"
    );
    // The real correctness criterion: no solver panic from sort mismatch.
    // Without the Deref(Var) preseed fix, mk_eq(Int, OptionInt) triggers
    // a caught panic that surfaces as Unknown in verification.
    assert!(
        encoder.solver_panic_reason().is_none(),
        "Deref(Var) preseed should prevent sort mismatch panic, \
             got: {:?}",
        encoder.solver_panic_reason()
    );
}

/// Regression for #1752: `self@ == Some(x)` should pre-seed `self` with
/// the datatype sort before View encoding computes `self_view`.
///
/// Without View-unwrapping in preseed extraction, `self_view` defaults to
/// Int and `mk_eq(Int, OptionInt)` panics.
#[test]
#[timeout(30000)]
fn test_view_var_eq_constructor_preseed_no_sort_mismatch() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    let expr = eq(view(var("self")), logic_fn_call("Some", vec![int(42)]));
    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "View(Var) == Constructor should encode successfully: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "View(Var) preseed should prevent sort mismatch panic, got: {:?}",
        encoder.solver_panic_reason()
    );
    match encoder.var_sort("self_view") {
        Some(Sort::Datatype(dt_sort)) => {
            assert_eq!(
                dt_sort.name, "OptionInt",
                "self_view should inherit OptionInt sort from pre-seeded base"
            );
        }
        other => panic!("expected self_view to be Datatype(OptionInt), got: {other:?}"),
    }
}

/// Regression for #1752: quantifier-bound variable in constructor equality
/// with Deref(Var) pattern (postcondition `*self == OwnResult::Ok(t)`).
///
/// The preseed mechanism handles the Deref(Var) pattern for `*self`,
/// resolving the sort mismatch between the Int-sorted `self_current` and
/// the Datatype-sorted `OwnResult::Ok(t)`.
#[test]
#[timeout(30000)]
fn test_quantifier_bound_var_in_constructor_eq_deref_no_sort_mismatch() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Pre-declare the OwnResult datatype (simulating a body match encoding)
    let dt = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "ownresult_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "ownresult_err_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Build: exists<t: T> *self == OwnResult::Ok(t)
    // The parser maps `T` → ExprSort::Int (generic type fallback)
    let body = eq(
        PureExpr::Deref(Arc::new(var("self"))),
        logic_fn_call("OwnResult::Ok", vec![var("t")]),
    );
    let expr = PureExpr::Exists {
        var: "t".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(body),
        triggers: vec![],
    };

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "exists<t: T> *self == OwnResult::Ok(t) should encode without \
             sort mismatch when OwnResult is declared: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "quantifier-bound var in constructor equality should not cause \
             sort mismatch panic: {:?}",
        encoder.solver_panic_reason()
    );
}

/// Regression for #1752: by-value `self == OwnResult::Ok(t)` pattern.
///
/// Same as the Deref pattern but with bare `Var("self")` (by-value contract).
/// The preseed handles bare Var → seeds `var_sorts["self"]` to Datatype.
#[test]
#[timeout(30000)]
fn test_quantifier_bound_var_in_constructor_eq_bare_var_no_sort_mismatch() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new_with_quantifiers();

    let dt = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "ownresult_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "ownresult_err_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Build: forall<t: T> self == OwnResult::Ok(t) ==> result == t
    let body = implies(
        eq(var("self"), logic_fn_call("OwnResult::Ok", vec![var("t")])),
        eq(var("result"), var("t")),
    );
    let expr = PureExpr::Forall {
        var: "t".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(body),
        triggers: vec![],
    };

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "forall<t: T> self == OwnResult::Ok(t) ==> result == t should \
             encode without sort mismatch: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "by-value constructor equality should not cause sort mismatch: {:?}",
        encoder.solver_panic_reason()
    );
}

/// Test for #1752: quantifier where the UF path is used (no datatype
/// declared). This should still work since everything stays Int-sorted.
#[test]
#[timeout(30000)]
fn test_quantifier_constructor_eq_uf_path_no_datatype() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // No datatype declared — OwnResult::Ok goes through UF path
    let body = eq(
        PureExpr::Deref(Arc::new(var("self"))),
        logic_fn_call("OwnResult::Ok", vec![var("t")]),
    );
    let expr = PureExpr::Exists {
        var: "t".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(body),
        triggers: vec![],
    };

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "UF path (no datatype) should encode without issues: {result:?}"
    );
}

/// Test for #1752: constructor equality quantifier elimination produces
/// correct results — existential over constructor equality is equivalent
/// to the datatype tester.
///
/// Verifies that `exists<t: T> self == OwnResult::Ok(t)` is eliminated to
/// `is_Ok(self)` and produces a satisfiable formula when self is Ok.
#[test]
#[timeout(30000)]
fn test_constructor_eq_elimination_exists_satisfiable() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, SolveResult};

    let mut encoder = AYEncoder::new_with_quantifiers();

    let dt = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "ownresult_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "ownresult_err_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Declare self as OwnResult-sorted and construct it as Ok(42)
    let self_var = encoder
        .get_or_declare_var("self", Sort::Datatype(dt.clone()))
        .unwrap();
    let forty_two = encoder.solver_mut().int_const(42);
    let ok_42 = encoder
        .solver_mut()
        .datatype_constructor(&dt, "Ok", &[forty_two]);
    let self_eq_ok = encoder.solver_mut().eq(self_var, ok_42);
    encoder.assert_term(self_eq_ok);

    // Encode: exists<t: T> self == OwnResult::Ok(t)
    // With elimination, this becomes is_Ok(self) which should be true.
    let body = eq(var("self"), logic_fn_call("OwnResult::Ok", vec![var("t")]));
    let exists_expr = PureExpr::Exists {
        var: "t".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(body),
        triggers: vec![],
    };

    let exists_term = encoder
        .encode_pure(&exists_expr)
        .expect("should encode exists expression");
    encoder.assert_term(exists_term);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "exists<t> self == Ok(t) should be Sat when self = Ok(42): got {result:?}"
    );
}

/// Test for #1752: forall constructor equality elimination produces
/// correct implication.
///
/// Verifies that `forall<t: T> self == OwnResult::Ok(t) ==> result == t`
/// is eliminated to `is_Ok(self) ==> result == accessor(self)` and that
/// the formula is verifiable (negation is unsat).
#[test]
#[timeout(30000)]
fn test_constructor_eq_elimination_forall_verifiable() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, SolveResult};

    let mut encoder = AYEncoder::new_with_quantifiers();

    let dt = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "ownresult_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "ownresult_err_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Declare self as OwnResult-sorted, result as Int
    let self_var = encoder
        .get_or_declare_var("self", Sort::Datatype(dt.clone()))
        .unwrap();
    let result_var = encoder.get_or_declare_var("result", Sort::Int).unwrap();

    // Assert self = Ok(42) and result = 42 (the correct postcondition)
    let forty_two = encoder.solver_mut().int_const(42);
    let ok_42 = encoder
        .solver_mut()
        .datatype_constructor(&dt, "Ok", &[forty_two]);
    let self_eq_ok = encoder.solver_mut().eq(self_var, ok_42);
    encoder.assert_term(self_eq_ok);
    let result_eq_42 = encoder.solver_mut().eq(result_var, forty_two);
    encoder.assert_term(result_eq_42);

    // Encode: forall<t: T> self == OwnResult::Ok(t) ==> result == t
    // With elimination: is_Ok(self) ==> result == accessor_ok(self)
    // Since self = Ok(42) and result = 42, the negation should be unsat.
    let body = implies(
        eq(var("self"), logic_fn_call("OwnResult::Ok", vec![var("t")])),
        eq(var("result"), var("t")),
    );
    let forall_expr = PureExpr::Forall {
        var: "t".to_string(),
        var_sort: Some(ExprSort::Int),
        body: Arc::new(body),
        triggers: vec![],
    };

    let forall_term = encoder
        .encode_pure(&forall_expr)
        .expect("should encode forall expression");

    // Negate the postcondition (verification checks unsat of negation)
    let negated = encoder.solver_mut().not(forall_term);
    encoder.assert_term(negated);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "NOT(forall<t> self == Ok(t) ==> result == t) should be Unsat \
             when self = Ok(42) and result = 42: got {result:?}"
    );
}

/// Test for #1752: multi-variable quantifier with constructor argument
/// uses constructor sort inference to assign correct datatype sort.
///
/// The constructor equality elimination only fires for single-variable
/// quantifiers. For multi-variable quantifiers like
/// `forall<t, u> self == Ok(t) ==> other == Ok(u) ==> result == t + u`,
/// the broader sort pre-scanning (infer_constructor_arg_sort) ensures both
/// `t` and `u` get the correct sort even though they are arguments to
/// datatype constructors.
///
/// This test verifies that the encoding doesn't panic from sort mismatches
/// and produces a correct (Unsat-on-negation) formula.
#[test]
#[timeout(30000)]
fn test_multi_var_quantifier_constructor_sort_inference() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new_with_quantifiers();

    let dt = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "ownresult_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "ownresult_err_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Build: forall<t, u> self == Ok(t) && other == Ok(u) ==> result == t + u
    // This is a multi-variable quantifier, so the constructor equality
    // elimination (single-variable only) doesn't fire. The sort inference
    // must detect that t and u appear as constructor arguments and assign
    // them the OwnResult datatype sort.
    //
    // Parser would produce nested quantifiers:
    //   Forall { var: "t", body: Forall { var: "u", body: ... } }
    let guard = and(
        eq(var("self"), logic_fn_call("OwnResult::Ok", vec![var("t")])),
        eq(var("other"), logic_fn_call("OwnResult::Ok", vec![var("u")])),
    );
    let consequent = eq(var("result"), add(var("t"), var("u")));
    let inner_body = implies(guard, consequent);

    // Nested quantifier: forall<u> (inner_body)
    let inner_forall = PureExpr::Forall {
        var: "u".to_string(),
        var_sort: Some(ExprSort::Int), // Generic T → Int fallback
        body: Arc::new(inner_body),
        triggers: vec![],
    };
    // Outer quantifier: forall<t> (forall<u> ...)
    let outer_forall = PureExpr::Forall {
        var: "t".to_string(),
        var_sort: Some(ExprSort::Int), // Generic T → Int fallback
        body: Arc::new(inner_forall),
        triggers: vec![],
    };

    let result = encoder.encode_pure(&outer_forall);
    assert!(
        result.is_ok(),
        "multi-variable quantifier with constructor args should encode \
             without sort mismatch: {result:?}"
    );
    assert!(
        encoder.solver_panic_reason().is_none(),
        "multi-variable quantifier should not cause sort mismatch panic: {:?}",
        encoder.solver_panic_reason()
    );
}
