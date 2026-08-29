// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::{super::*, helpers::*};

#[test]
#[timeout(30000)]
fn shared_spec_unwrap_preserves_some_and_ok_values_in_one_query() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let some_unwrap_term = encoder
        .encode_pure(&method_call(
            logic_fn_call("Some", vec![int(42)]),
            "unwrap",
            vec![],
        ))
        .expect("Some(42).unwrap() should encode");
    let ok_unwrap_term = encoder
        .encode_pure(&method_call(
            logic_fn_call("Ok", vec![int(99)]),
            "unwrap",
            vec![],
        ))
        .expect("Ok(99).unwrap() should encode");

    encoder.assert_option_result_axioms();

    let forty_two = encoder.encode_pure(&int(42)).expect("42 should encode");
    let ninety_nine = encoder.encode_pure(&int(99)).expect("99 should encode");

    let any_unwrap_mismatch = {
        let solver = encoder.solver_mut();
        let some_eq = solver.eq(some_unwrap_term, forty_two);
        let some_mismatch = solver.not(some_eq);
        let ok_eq = solver.eq(ok_unwrap_term, ninety_nine);
        let ok_mismatch = solver.not(ok_eq);
        solver.or(some_mismatch, ok_mismatch)
    };
    encoder.assert_term(any_unwrap_mismatch);

    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "Shared spec_unwrap should preserve both Some and Ok unwrap values simultaneously"
    );
}

fn sat_result_for_is_some_of_ok(include_is_ok_conjunct: bool) -> SolveResult {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let ok_value = logic_fn_call("Ok", vec![int(42)]);

    let is_some_term = encoder
        .encode_pure(&method_call(ok_value.clone(), "is_some", vec![]))
        .expect("is_some(Ok(42)) should encode");

    let asserted_term = if include_is_ok_conjunct {
        let is_ok_term = encoder
            .encode_pure(&method_call(ok_value, "is_ok", vec![]))
            .expect("is_ok(Ok(42)) should encode");
        let solver = encoder.solver_mut();
        solver.and(is_some_term, is_ok_term)
    } else {
        is_some_term
    };

    encoder.assert_option_result_axioms();
    encoder.assert_term(asserted_term);
    encoder.check_sat()
}

#[test]
#[timeout(30000)]
fn is_some_ok_query_matches_explicit_is_ok_conjunction() {
    let single_tester_result = sat_result_for_is_some_of_ok(false);
    let conjunction_result = sat_result_for_is_some_of_ok(true);

    assert!(
        matches!(
            (&single_tester_result, &conjunction_result),
            (SolveResult::Sat, SolveResult::Sat) | (SolveResult::Unsat(_), SolveResult::Unsat(_))
        ),
        "Adding explicit is_ok(Ok(42)) conjunct should not change satisfiability: \
         single={single_tester_result:?}, conjunction={conjunction_result:?}"
    );
}
