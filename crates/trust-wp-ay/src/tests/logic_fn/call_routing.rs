// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

#[test]
#[timeout(30000)]
fn test_encode_logic_fn_call_simple() {
    // Test encoding a simple logic function call: max(x, y)
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("max", vec![var("x"), var("y")]);

    let term = encoder
        .encode_pure(&expr)
        .expect("Should encode LogicFnCall");

    // Semantic: max(x, y) == max(x, y) is a tautology (UF congruence)
    let term2 = encoder.encode_pure(&expr).expect("re-encode same call");
    let eq = encoder.solver.eq(term, term2);
    let neg = encoder.solver.not(eq);
    encoder.assert_term(neg);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "max(x,y) != max(x,y) should be UNSAT (UF congruence)"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_logic_fn_call_nullary() {
    // Test encoding a nullary logic function: zero_constant()
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("zero_constant", vec![]);

    let term = encoder
        .encode_pure(&expr)
        .expect("Should encode nullary call");

    // Semantic: zero_constant() == zero_constant() (UF congruence on nullary)
    let term2 = encoder.encode_pure(&expr).expect("re-encode nullary");
    let eq = encoder.solver.eq(term, term2);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "zero_constant() != zero_constant() should be UNSAT"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_logic_fn_call_qualified_name() {
    // Test that qualified names like "crate::specs::max" work
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("crate::specs::max", vec![int(1), int(2)]);

    let term = encoder
        .encode_pure(&expr)
        .expect("Should encode qualified name");

    // Semantic: same call produces the same term (functional consistency)
    let term2 = encoder.encode_pure(&expr).expect("re-encode qualified");
    let eq = encoder.solver.eq(term, term2);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "qualified fn with same args should return same value"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_logic_fn_call_reuses_declaration() {
    // Test that calling the same function twice reuses the declaration
    let mut encoder = AYEncoder::new();

    let call1 = logic_fn_call("max", vec![var("x"), var("y")]);

    let call2 = logic_fn_call("max", vec![var("a"), var("b")]);

    // Both should succeed
    let term1 = encoder
        .encode_pure(&call1)
        .expect("First call should encode");
    let term2 = encoder
        .encode_pure(&call2)
        .expect("Second call should reuse decl");

    // Should have exactly one function declaration for "max"
    assert_eq!(
        encoder.decls().logic_func_count(),
        1,
        "Should have one declaration"
    );
    let decl_names = encoder.decls().logic_func_names().collect::<Vec<_>>();
    assert!(
        decl_names
            .iter()
            .any(|name| name.starts_with("logic_max__placeholder_")),
        "Should reuse one signature-keyed placeholder declaration; found: {:?}",
        decl_names
    );

    // Semantic: max(x,y) and max(a,b) are distinct calls — they CAN differ
    // (when x≠a or y≠b), so asserting inequality should be SAT
    let eq = encoder.solver.eq(term1, term2);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "max(x,y) != max(a,b) should be SAT (different args can differ)"
    );
}

#[test]
#[timeout(30000)]
fn test_bool_logic_fn_eq_uses_biconditional_semantics() {
    use ay_dpll::api::{SolveResult, Sort};
    use trust_wp_core::logic::logic_fn_smt_name;

    let mut encoder = AYEncoder::new();
    let left_smt = logic_fn_smt_name("pred_left");
    let right_smt = logic_fn_smt_name("pred_right");
    let left_decl = encoder
        .solver
        .declare_fun(&left_smt, &[Sort::Int], Sort::Bool);
    let right_decl = encoder
        .solver
        .declare_fun(&right_smt, &[Sort::Int], Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(left_smt, left_decl);
    encoder
        .decls_for_test_mut()
        .insert_logic_func(right_smt, right_decl);

    let left_expr = logic_fn_call("pred_left", vec![var("x")]);
    let right_expr = logic_fn_call("pred_right", vec![var("x")]);
    let eq_expr = eq(left_expr.clone(), right_expr.clone());

    let eq_term = encoder
        .encode_pure(&eq_expr)
        .expect("Bool logic-fn equality should encode");
    let left_term = encoder
        .encode_pure(&left_expr)
        .expect("left Bool logic-fn call should encode");
    let right_term = encoder
        .encode_pure(&right_expr)
        .expect("right Bool logic-fn call should encode");
    let not_right = encoder.solver.not(right_term);

    encoder.assert_term(left_term);
    encoder.assert_term(not_right);
    encoder.assert_term(eq_term);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "p=true, q=false, and (p == q) must be UNSAT with iff-based Bool equality"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_logic_fn_call_with_prefix() {
    // Test encoding logic function call in old() context
    let mut encoder = AYEncoder::new();

    let call = logic_fn_call("max", vec![var("x"), var("y")]);

    // In old() context, variables get "old_" prefix but function name doesn't
    // Wrap in Old to test the prefixed encoding path
    let old_call = old(call.clone());
    let old_term = encoder
        .encode_pure(&old_call)
        .expect("Should encode old() prefix");

    // Semantic: old(max(x,y)) and max(x,y) use different variable namespaces
    // (old_x vs x), so they CAN differ — inequality should be SAT
    let direct_term = encoder.encode_pure(&call).expect("encode direct call");
    let eq = encoder.solver.eq(old_term, direct_term);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Sat),
        "old(max(x,y)) != max(x,y) should be SAT (different var namespaces)"
    );
}

#[test]
#[timeout(30000)]
fn test_encode_logic_fn_call_nested_args() {
    // Test encoding logic function with complex arguments
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("max", vec![add(var("x"), int(1)), var("y")]);

    let term = encoder
        .encode_pure(&expr)
        .expect("Should encode nested args");

    // Semantic: max(x+1, y) with the same call should be identical (UF congruence)
    let term2 = encoder.encode_pure(&expr).expect("re-encode nested args");
    let eq = encoder.solver.eq(term, term2);
    let neq = encoder.solver.not(eq);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "max(x+1,y) != max(x+1,y) should be UNSAT (UF congruence)"
    );
}

/// Regression test: encoding `LetAssume { match ... Err(true) ... }` followed
/// by `eq(var, Err(true))` should not panic with sort mismatch.
///
/// Reproduces the ok_or(true) proof_assert scenario from option.rs (#1277):
/// The match postcondition declares ResultIntInt via match_datatype, then
/// the assertion encodes Err(true) via datatype constructor with Bool→Int
/// coercion. The sort mismatch occurs if the match arm body encodes
/// Err(true) in a context where the Bool payload isn't coerced.
///
/// NOTE: encoding-only — LetAssume match encoding produces side-effect assertions
/// on internal state markers; check_sat would test the state marker machinery
/// rather than the Bool→Int coercion regression this test guards. See #1990.
#[test]
#[timeout(30000)]
fn test_let_assume_match_err_bool_then_eq_err_bool_no_sort_panic() {
    let mut encoder = AYEncoder::new();

    // Simulate ok_or(true) postcondition:
    // match *self {
    //   Some(v) => result == Ok(v),
    //   None => result == Err(true),
    // }
    let postcondition = match_expr(
        deref(var("self_opt")),
        vec![
            (
                Pattern::Constructor {
                    name: "Some".to_string(),
                    inner: Some(Box::new(Pattern::Binding("v".to_string()))),
                },
                eq(var("result"), logic_fn_call("Ok", vec![var("v")])),
            ),
            (
                Pattern::Constructor {
                    name: "None".to_string(),
                    inner: None,
                },
                eq(var("result"), logic_fn_call("Err", vec![bool_expr(true)])),
            ),
        ],
    );

    // The body expression tree: LetAssume(postcondition, state_marker)
    let body_with_assumption = let_assume(postcondition, int(0));

    // Encode the body result (this asserts the postcondition match as an assumption)
    let _body_term = encoder
        .encode_pure(&body_with_assumption)
        .expect("LetAssume with match Err(true) postcondition should encode without panic");

    // Now encode the proof_assert assertion: err_local == Err(true)
    let assertion = eq(
        var("err_local"),
        logic_fn_call("Err", vec![bool_expr(true)]),
    );
    let _assertion_term = encoder
        .encode_pure(&assertion)
        .expect("eq(err_local, Err(true)) should encode after match postcondition");
}

/// Qualified constructor names (e.g., "OwnResult::Ok") should resolve to the
/// native datatype constructor path when the corresponding ADT is declared.
///
/// Before #1296 fix: `constructor_datatype("OwnResult::Ok")` returned `None`
/// because it compared "OwnResult::Ok" against short constructor names ("Ok"),
/// causing a fallback to uninterpreted functions. This meant postcondition
/// quantifiers over user-defined enums used UF encoding while match bodies
/// used datatype encoding — an incompatibility that made ay return "unknown".
#[test]
#[timeout(30000)]
fn test_encode_logic_fn_call_qualified_constructor_uses_datatype_path() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new();

    // Declare a user-defined OwnResult datatype (simulating what match
    // encoding produces for `enum OwnResult<T, E> { Ok(T), Err(E) }`).
    let own_result = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_err_error".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&own_result);

    // Encode qualified constructor call: OwnResult::Ok(42)
    let qualified_ok = logic_fn_call("OwnResult::Ok", vec![int(42)]);
    let qualified_ok_term = encoder
        .encode_pure(&qualified_ok)
        .expect("OwnResult::Ok(42) should encode via datatype constructor path");

    // Encode unqualified constructor call: Ok(42) — should also use datatype path
    let unqualified_ok = logic_fn_call("Ok", vec![int(42)]);
    let unqualified_ok_term = encoder
        .encode_pure(&unqualified_ok)
        .expect("Ok(42) should encode via datatype constructor path");

    // Both should produce the same term (both route through datatype constructor)
    let eq_term = encoder.solver.eq(qualified_ok_term, unqualified_ok_term);
    let neq = encoder.solver.not(eq_term);
    encoder.assert_term(neq);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "OwnResult::Ok(42) and Ok(42) should be identical datatype constructor applications"
    );
}

/// When two different user-defined enums share constructor names, a qualified
/// name should only match the correct ADT, not the first one found.
#[test]
#[timeout(30000)]
fn test_constructor_datatype_qualified_name_selects_correct_adt() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new();

    // Declare two datatypes that both have an "Ok" constructor
    let own_result = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Ok".to_string(),
            fields: vec![DatatypeField {
                name: "own_result_ok_value".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    let other_result = DatatypeSort {
        name: "OtherResult".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Ok".to_string(),
            fields: vec![DatatypeField {
                name: "other_result_ok_value".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    encoder.ensure_datatype_declared(&own_result);
    encoder.ensure_datatype_declared(&other_result);

    // "OwnResult::Ok" should match the OwnResult datatype
    let dt = encoder.constructor_datatype("OwnResult::Ok");
    assert!(dt.is_some(), "OwnResult::Ok should find a datatype");
    assert_eq!(
        dt.unwrap().name,
        "OwnResult",
        "OwnResult::Ok should match the OwnResult datatype, not OtherResult"
    );

    // "OtherResult::Ok" should match the OtherResult datatype
    let dt2 = encoder.constructor_datatype("OtherResult::Ok");
    assert!(dt2.is_some(), "OtherResult::Ok should find a datatype");
    assert_eq!(
        dt2.unwrap().name,
        "OtherResult",
        "OtherResult::Ok should match the OtherResult datatype, not OwnResult"
    );
}

/// Qualified custom constructors must not silently fall back to the stdlib
/// Result datatype when both are declared. Regresses the residual #2462
/// `OwnResult::Ok` routing bug that survived the result-inference fix.
#[test]
#[timeout(30000)]
fn test_constructor_datatype_qualified_custom_result_ignores_stdlib_result() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new();

    let std_result = DatatypeSort {
        name: "ResultIntInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "result_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "result_err_error".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    let own_result = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_ok_value".to_string(),
                    sort: Sort::Uninterpreted("T".to_string()),
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_err_value".to_string(),
                    sort: Sort::Uninterpreted("E".to_string()),
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&std_result);
    encoder.ensure_datatype_declared(&own_result);

    let dt = encoder.constructor_datatype("OwnResult::Ok");
    assert!(dt.is_some(), "OwnResult::Ok should find a datatype");
    assert_eq!(
        dt.unwrap().name,
        "OwnResult",
        "qualified custom constructor should prefer OwnResult over ResultIntInt"
    );
}

/// Placeholder declaration for a function with a Seq sort hint should get
/// Seq return sort instead of the default Int. Before #994 fix, only Bool
/// hints were checked; Seq and FMap hints were ignored, causing sort
/// mismatches when the placeholder function was used in Seq contexts.
#[test]
#[timeout(30000)]
fn test_placeholder_fn_with_seq_hint_gets_seq_return_sort() {
    let mut encoder = AYEncoder::new();

    // Pre-register a Seq sort hint for the function name. This simulates
    // what happens during prescan when a function appears in a Seq context
    // (e.g., its return value has .len() called on it).
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("get_items");
    encoder.record_sort_hint(smt_name, trust_wp_core::formula::ExprSort::Seq);

    // Encode a call to the unregistered function — this triggers the
    // placeholder path in apply_logic_fn.
    let call = logic_fn_call("get_items", vec![int(1)]);
    let term = encoder
        .encode_pure(&call)
        .expect("get_items(1) placeholder should encode without error");

    // The placeholder's return sort should be Seq (not Int).
    let term_sort = encoder.solver.get_sort(term);
    assert!(
        term_sort.is_seq(),
        "Expected Seq return sort for placeholder with Seq hint, got {term_sort:?}"
    );
}

/// Placeholder declaration for a function with an FMap sort hint should get
/// FMap return sort instead of the default Int. (#994)
#[test]
#[timeout(30000)]
fn test_placeholder_fn_with_fmap_hint_gets_fmap_return_sort() {
    let mut encoder = AYEncoder::new();

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("get_mapping");
    encoder.record_sort_hint(smt_name, trust_wp_core::formula::ExprSort::FMap);

    let call = logic_fn_call("get_mapping", vec![int(1)]);
    let term = encoder
        .encode_pure(&call)
        .expect("get_mapping(1) placeholder should encode without error");

    let term_sort = encoder.solver.get_sort(term);
    assert!(
        matches!(term_sort, ay_dpll::api::Sort::Uninterpreted(ref s) if s == "FMap"),
        "Expected FMap return sort for placeholder with FMap hint, got {term_sort:?}"
    );
}

/// Regression test for #2565: when a placeholder arg_expr infers as non-Int
/// (via `constructor_datatype` lookup in `infer_encoded_sort`) but the actual
/// pre-encoded arg_term is Int-sorted (because the inner call went through the
/// UF fallback path), the placeholder domain must use the actual term sort.
///
/// Before fix: the reconciliation only caught `inferred=Int, actual≠Int`.
/// The reverse (`inferred≠Int, actual=Int`) was missed, causing a domain sort
/// mismatch in `safe_apply` — the declaration domain expected Datatype but
/// the arg_term had Int.
#[test]
#[timeout(30000)]
fn test_placeholder_reconciles_non_int_inferred_vs_int_actual_arg_sort() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new();

    // Declare a datatype so that `constructor_datatype("CustomEnum::Variant")`
    // returns Some, making `infer_encoded_sort` return Sort::Datatype(CustomEnum)
    // for LogicFnCall("CustomEnum::Variant", ...) expressions.
    let custom_enum = DatatypeSort {
        name: "CustomEnum".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Variant".to_string(),
            fields: vec![DatatypeField {
                name: "custom_enum_variant_value".to_string(),
                sort: Sort::Uninterpreted("T".to_string()),
            }],
        }],
    };
    encoder.ensure_datatype_declared(&custom_enum);

    // Create an Int-sorted term — simulates the result of encoding the inner
    // constructor call through the UF fallback path (not the native datatype
    // constructor path). In production this happens when native_constructor_call
    // bails due to field sort mismatch (e.g., OwnResult::<&mut T, E>::copied).
    let int_term = encoder.solver.int_const(42);

    // The arg_expr is a qualified constructor call. infer_expr_sort_with_context
    // will fall through to infer_encoded_sort → constructor_datatype →
    // Sort::Datatype(CustomEnum). But the arg_term is Int.
    let arg_expr = logic_fn_call("CustomEnum::Variant", vec![var("x")]);

    // Without the bidirectional reconciliation fix (#2565), this panics with:
    //   "sort mismatch in logic_fn_placeholder:target_fn: expected matching
    //    domain sort, got Int"
    let result = encoder.apply_logic_fn("target_fn", &[int_term], Some(&[arg_expr]), None);
    assert!(
        result.is_ok(),
        "placeholder should reconcile non-Int inferred vs Int actual arg sort (#2565): {result:?}"
    );
}

/// End-to-end regression for #2565: encoding `OwnResult::Ok(InnerEnum::Wrap(42))`
/// where OwnResult has non-Int field sorts and InnerEnum::Wrap falls through
/// to UF (producing Int). The outer OwnResult::Ok placeholder must reconcile
/// the inferred Datatype arg sort against the actual Int term sort.
#[test]
#[timeout(30000)]
fn test_own_result_ok_with_uf_fallback_inner_constructor_no_sort_panic() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

    let mut encoder = AYEncoder::new();

    // OwnResult with Uninterpreted("T") field — native constructor will bail
    // for Int-sorted args.
    let own_result = DatatypeSort {
        name: "OwnResult".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_ok_value".to_string(),
                    sort: Sort::Uninterpreted("T".to_string()),
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "own_result_err_error".to_string(),
                    sort: Sort::Uninterpreted("E".to_string()),
                }],
            },
        ],
    };
    // InnerEnum with Uninterpreted("T") field — native constructor will also bail.
    let inner_enum = DatatypeSort {
        name: "InnerEnum".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Wrap".to_string(),
            fields: vec![DatatypeField {
                name: "inner_enum_wrap_value".to_string(),
                sort: Sort::Uninterpreted("T".to_string()),
            }],
        }],
    };
    encoder.ensure_datatype_declared(&own_result);
    encoder.ensure_datatype_declared(&inner_enum);

    // Encode OwnResult::Ok(InnerEnum::Wrap(42))
    // - InnerEnum::Wrap(42): native constructor bails (field Uninterpreted("T") ≠ Int)
    //   → UF placeholder → Int-sorted term
    // - OwnResult::Ok(<Int-sorted term>): native constructor bails
    //   (field Uninterpreted("T") ≠ Int) → UF placeholder path
    // - In apply_logic_fn for OwnResult::Ok:
    //   infer_expr_sort_with_context on InnerEnum::Wrap(...) → Datatype(InnerEnum)
    //   But actual arg_term sort is Int → bidirectional reconciliation needed
    let expr = logic_fn_call(
        "OwnResult::Ok",
        vec![logic_fn_call("InnerEnum::Wrap", vec![int(42)])],
    );

    let result = encoder.encode_pure(&expr);
    assert!(
        result.is_ok(),
        "OwnResult::Ok(InnerEnum::Wrap(42)) should encode without sort mismatch (#2565): \
         {result:?}"
    );
}

/// Reproduces the option.rs ok_or proof_assert failure scenario.
///
/// The proof_assert pipeline produces:
///   ghost_context: [err == call_3, none == None(), some == Some(1)]
///   requires:      [err == call_3, none == None(), some == Some(1),
///                    Bool(true), call_3 == Err(true)]
///   ensures:       [call_3 == Err(true)]
///
/// The ghost_context assertion `err == call_3` encodes as `eq(Int, ResultIntInt)`
/// because `err` has no sort evidence and defaults to Int, while `call_3` is
/// pre-declared as ResultIntInt from the constructor equality in ensures.
/// Sort coercion replaces the Int side with an unconstrained fresh constant,
/// disconnecting `err` from `call_3`.
///
/// The precondition `call_3 == Err(true)` should still constrain `call_3`
/// directly, making the ensures `call_3 == Err(true)` trivially provable.
/// This test verifies that the full pipeline handles this correctly.
///
/// Part of #2653: option.rs compat test failure investigation.
#[test]
#[timeout(30000)]
fn test_proof_assert_ok_or_ghost_context_sort_mismatch() {
    use crate::{verify_function_with_modes, VerificationRequest, VerificationResult};

    // Ghost context: alias facts from the proof_assert snapshot
    let ghost_context = vec![
        eq(var("err"), var("call_3")),
        eq(var("none"), logic_fn_call("None", vec![])),
        eq(var("some"), logic_fn_call("Some", vec![int(1)])),
    ];

    // Requires: ghost facts + reduced assumed facts
    let requires = vec![
        // Ghost alias facts (duplicated in requires)
        eq(var("err"), var("call_3")),
        eq(var("none"), logic_fn_call("None", vec![])),
        eq(var("some"), logic_fn_call("Some", vec![int(1)])),
        // Vacuously true (reduced from: None().is_some() ==> ...)
        bool_expr(true),
        // Reduced from: None().is_none() ==> (call_3 == Err(true))
        eq(var("call_3"), logic_fn_call("Err", vec![bool_expr(true)])),
    ];

    // Ensures: the proof_assert assertion
    let ensures = vec![eq(
        var("call_3"),
        logic_fn_call("Err", vec![bool_expr(true)]),
    )];

    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures).ghost_context(Some(&ghost_context)),
    );

    assert!(result.is_ok(), "should not error: {result:?}");
    let vr = result.unwrap();
    // This must be Verified — the assertion is literally a precondition.
    // If it fails, the ghost_context sort coercion is corrupting call_3.
    assert!(
        matches!(vr, VerificationResult::Verified(_)),
        "call_3 == Err(true) should verify when it appears as both \
         requires and ensures: got {vr:?}"
    );
}
