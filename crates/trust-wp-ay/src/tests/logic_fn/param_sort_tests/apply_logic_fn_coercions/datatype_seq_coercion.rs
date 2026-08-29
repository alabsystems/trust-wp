// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test that calling a Datatype-parameterized logic function with a
/// Seq-sorted argument does not panic. (#2002)
///
/// When List::sum(self) is declared with Sort::Datatype parameter (from
/// match-pattern inference), but the call-site variable `l` was declared
/// as Seq (from View encoding or first-declaration-wins lock-in), the
/// apply_logic_fn coercion should produce a fresh constant instead of
/// crashing with a ay sort mismatch.
#[test]
#[timeout(30000)]
fn test_apply_logic_fn_coerces_seq_arg_to_datatype_param() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register the List datatype and sum function (same as above test)
    let body = PureExpr::Match {
        scrutinee: Arc::new(var("self")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "List::Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("a".to_string()),
                        Pattern::Binding("l".to_string()),
                    ]))),
                },
                body: var("a"),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "List::Nil".to_string(),
                    inner: None,
                },
                body: int(0),
            },
        ],
    };

    let logic_fn = LogicFnDef::new(
        "sum".to_string(),
        "List::sum".to_string(),
        vec!["self".to_string()],
        body,
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("register List::sum");

    // Now simulate a call-site where `l` is Seq-sorted (from View encoding).
    // Use the canonical native Seq sort that current inference produces.
    let seq_sort = Sort::seq(Sort::Int);
    let l_term = encoder
        .get_or_declare_var("l_view", seq_sort)
        .expect("declare l_view as Seq");

    // Calling apply_logic_fn with a Seq-sorted term should NOT panic —
    // the coercion should replace it with a fresh Datatype-sorted constant.
    let result = encoder.apply_logic_fn("sum", &[l_term], None, None);
    assert!(
        result.is_ok(),
        "apply_logic_fn should coerce Seq→Datatype without panic (#2002): {result:?}"
    );
}

/// Mismatched argument coercion in `apply_logic_fn` must record a
/// non-demoting unsoundness counter (SortCoercionBridge) for observability.
/// The coercion replaces the argument with a fresh unconstrained constant,
/// which is strictly conservative (cannot produce false proofs). (#2357)
#[test]
#[timeout(30000)]
fn test_apply_logic_fn_coercion_records_unsoundness_counter() {
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};

    unsoundness::reset();
    let before = unsoundness::snapshot();

    let mut encoder = AYEncoder::new_with_quantifiers();

    let seq_sort = Sort::seq(Sort::Int);
    let func_decl =
        encoder
            .solver
            .declare_fun("logic_g", std::slice::from_ref(&seq_sort), Sort::Bool);
    encoder
        .decls_for_test_mut()
        .insert_logic_func("logic_g".to_string(), func_decl);

    let bool_term = encoder.solver.bool_const(true);
    let result = encoder.apply_logic_fn("g", &[bool_term], None, None);
    assert!(
        result.is_ok(),
        "apply_logic_fn should coerce Bool → Seq without panic: {result:?}"
    );

    let after = unsoundness::snapshot();
    let delta = unsoundness::delta(&before, &after);
    assert!(
        delta
            .get(&UnsoundnessCategory::SortCoercionBridge)
            .copied()
            .unwrap_or(0)
            > 0,
        "apply_logic_fn coercion must fire SortCoercionBridge (#2357). Delta: {delta:?}"
    );

    unsoundness::reset();
}

/// Soundness audit: apply_logic_fn coercion must not cause false
/// verification. (#2002)
///
/// When the coercion replaces an argument with a fresh unconstrained
/// constant, the function application `f(fresh_const)` is disconnected
/// from the original argument. This test verifies that the disconnection
/// makes postconditions HARDER to prove (conservative), not easier
/// (unsound). Specifically: asserting `sum(list) == 42` should not be
/// satisfiable when `list` is coerced away, because the solver has no
/// constraints linking the fresh constant to any specific value.
#[test]
#[timeout(30000)]
fn test_apply_logic_fn_coercion_does_not_cause_false_sat() {
    use trust_wp_core::formula::{MatchArm, Pattern};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register the List datatype with a sum function, same as above.
    let body = PureExpr::Match {
        scrutinee: Arc::new(var("self")),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "List::Cons".to_string(),
                    inner: Some(Box::new(Pattern::Tuple(vec![
                        Pattern::Binding("a".to_string()),
                        Pattern::Binding("l".to_string()),
                    ]))),
                },
                body: var("a"),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "List::Nil".to_string(),
                    inner: None,
                },
                body: int(0),
            },
        ],
    };

    let logic_fn = LogicFnDef::new(
        "sum".to_string(),
        "List::sum".to_string(),
        vec!["self".to_string()],
        body,
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("register List::sum");

    // Create a Seq-sorted variable (triggers coercion when passed to sum).
    let seq_sort = Sort::seq(Sort::Int);
    let l_term = encoder
        .get_or_declare_var("l_view", seq_sort)
        .expect("declare l_view as Seq");

    // Call sum(l_view) — this triggers coercion. The coerced call
    // produces sum(fresh_const) where fresh_const is unconstrained
    // and has no relationship to l_view.
    let sum_result = encoder
        .apply_logic_fn("sum", &[l_term], None, None)
        .expect("apply_logic_fn should succeed with coercion");

    // Assert the NEGATION: NOT(sum(coerced_arg) == 0).
    // In the verification pipeline, this corresponds to negating the
    // postcondition. If we get UNSAT, it means the postcondition was
    // "verified" — which would be a false positive since the argument
    // was coerced away to an unconstrained fresh constant.
    let zero = encoder.solver.int_const(0);
    let sum_eq_zero = encoder.solver.eq(sum_result, zero);
    let not_sum_eq_zero = encoder.solver.not(sum_eq_zero);
    encoder.solver.assert_term(not_sum_eq_zero);

    let sat = encoder.solver.check_sat();
    let unknown_reason = encoder.solver.unknown_reason();
    let solve_stats = format!("{:?}", encoder.solver.statistics());
    let assertions = encoder
        .solver
        .assertions()
        .into_iter()
        .map(|term| encoder.solver.format_term(term))
        .collect::<Vec<_>>();
    // SAT means verification fails; Unknown is also conservative under latest
    // ay. UNSAT would mean the coercion allowed a false verification.
    assert!(
        !sat.is_unsat(),
        "NOT(sum(coerced_arg) == 0) must not be UNSAT. UNSAT here would mean \
         the coercion caused a false verification - unsound! Got: {sat:?}; \
         unknown_reason={unknown_reason:?}; solve_stats={solve_stats:?}; \
         assertions={assertions:#?}"
    );
}
