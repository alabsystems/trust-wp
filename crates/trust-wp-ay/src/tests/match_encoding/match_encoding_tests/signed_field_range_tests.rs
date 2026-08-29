// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match expression encoding tests for trust-wp-ay.

use super::*;

// ── Signed field range constraint tests (#2178 Prover coverage) ───

/// With signed(32) range hints, the field allows negative values within
/// the i32 range. `field == -1` should be satisfiable.
#[test]
#[timeout(30000)]
fn test_adt_field_signed_range_allows_negative() {
    use std::collections::HashMap;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    use trust_wp_core::logic::FieldRangeKind;

    let mut encoder = AYEncoder::new_all();

    let mut ranges = HashMap::new();
    ranges.insert(
        "Wrapper".to_string(),
        vec![("Wrap".to_string(), vec![(0, FieldRangeKind::Signed(32))])],
    );
    let dt = DatatypeSort {
        name: "Wrapper".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Wrap".to_string(),
            fields: vec![DatatypeField {
                name: "wrapper_wrap_0".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    encoder.ensure_datatype_declared(&dt);
    encoder.set_adt_field_ranges(ranges);

    let neg_one = encoder.solver.int_const(-1);
    let x = encoder.solver.datatype_constructor(&dt, "Wrap", &[neg_one]);
    let is_wrap = encoder
        .solver
        .try_datatype_tester("Wrap", x)
        .expect("tester");
    encoder.solver.assert_term(is_wrap);

    let field_val = encoder
        .solver
        .try_datatype_selector("wrapper_wrap_0", x, Sort::Int)
        .expect("selector");

    let min_i32 = encoder.solver.int_const(i64::from(i32::MIN));
    let max_i32 = encoder.solver.int_const(i64::from(i32::MAX));
    let ge_min = encoder.solver.ge(field_val, min_i32);
    let le_max = encoder.solver.le(field_val, max_i32);
    encoder.solver.assert_term(ge_min);
    encoder.solver.assert_term(le_max);

    // Assert field == -1 — satisfiable within i32 range.
    let eq_neg_one = encoder.solver.eq(field_val, neg_one);
    encoder.solver.assert_term(eq_neg_one);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "With signed(32) range hint, field == -1 should be SAT: {result:?}"
    );
}

/// With signed(32) range hints, the field is bounded below at -2^31.
/// `field == -2147483649` (one below i32::MIN) should be unsatisfiable.
#[test]
#[timeout(30000)]
fn test_adt_field_signed_range_blocks_below_min() {
    use std::collections::HashMap;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    use trust_wp_core::logic::FieldRangeKind;

    let mut encoder = AYEncoder::new_all();

    let mut ranges = HashMap::new();
    ranges.insert(
        "Wrapper".to_string(),
        vec![("Wrap".to_string(), vec![(0, FieldRangeKind::Signed(32))])],
    );
    encoder.set_adt_field_ranges(ranges);

    let dt = DatatypeSort {
        name: "Wrapper".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Wrap".to_string(),
            fields: vec![DatatypeField {
                name: "wrapper_wrap_0".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    encoder.ensure_datatype_declared(&dt);

    let x = encoder
        .get_or_declare_var("x", Sort::Datatype(dt.clone()))
        .unwrap();
    let is_wrap = encoder
        .solver
        .try_datatype_tester("Wrap", x)
        .expect("tester");
    encoder.solver.assert_term(is_wrap);

    let field_val = encoder
        .solver
        .try_datatype_selector("wrapper_wrap_0", x, Sort::Int)
        .expect("selector");

    // Assert field == -2147483649 (i32::MIN - 1) — should be UNSAT
    let below_min = encoder.solver.int_const(-2_147_483_649i64);
    let eq_below = encoder.solver.eq(field_val, below_min);
    encoder.solver.assert_term(eq_below);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "With signed(32) range hint, field == i32::MIN - 1 should be UNSAT: {result:?}"
    );
}

/// With signed(32) range hints, the field is bounded above at 2^31 - 1.
/// `field == 2147483648` (one above i32::MAX) should be unsatisfiable.
#[test]
#[timeout(30000)]
fn test_adt_field_signed_range_blocks_above_max() {
    use std::collections::HashMap;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    use trust_wp_core::logic::FieldRangeKind;

    let mut encoder = AYEncoder::new_all();

    let mut ranges = HashMap::new();
    ranges.insert(
        "Wrapper".to_string(),
        vec![("Wrap".to_string(), vec![(0, FieldRangeKind::Signed(32))])],
    );
    encoder.set_adt_field_ranges(ranges);

    let dt = DatatypeSort {
        name: "Wrapper".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Wrap".to_string(),
            fields: vec![DatatypeField {
                name: "wrapper_wrap_0".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    encoder.ensure_datatype_declared(&dt);

    let x = encoder
        .get_or_declare_var("x", Sort::Datatype(dt.clone()))
        .unwrap();
    let is_wrap = encoder
        .solver
        .try_datatype_tester("Wrap", x)
        .expect("tester");
    encoder.solver.assert_term(is_wrap);

    let field_val = encoder
        .solver
        .try_datatype_selector("wrapper_wrap_0", x, Sort::Int)
        .expect("selector");

    // Assert field == 2147483648 (i32::MAX + 1) — should be UNSAT
    let above_max = encoder.solver.int_const(2_147_483_648i64);
    let eq_above = encoder.solver.eq(field_val, above_max);
    encoder.solver.assert_term(eq_above);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "With signed(32) range hint, field == i32::MAX + 1 should be UNSAT: {result:?}"
    );
}
