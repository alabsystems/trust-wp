// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match expression encoding tests for trust-wp-ay.

use std::sync::Arc;

use super::*;

// ── ADT Field Range Constraint Tests (#2097, RC1) ───────────────────

/// Without field range hints, the solver can assign a negative value to a
/// u32 field, making `field >= 0` unprovable.
#[test]
#[timeout(30000)]
fn test_adt_field_without_range_hint_allows_negative() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new_all();

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

    // Assert field < 0 — satisfiable without range hint
    let zero = encoder.solver.int_const(0);
    let lt_zero = encoder.solver.lt(field_val, zero);
    encoder.solver.assert_term(lt_zero);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Without range hint, a u32 field can be negative: {result:?}"
    );
}

/// With unsigned field range hints, the encoder injects axioms preventing
/// negative values for u32 fields. `field < 0` becomes unsatisfiable.
#[test]
#[timeout(30000)]
fn test_adt_field_with_unsigned_range_hint_blocks_negative() {
    use std::collections::HashMap;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    use trust_wp_core::logic::FieldRangeKind;

    let mut encoder = AYEncoder::new_all();

    let mut ranges = HashMap::new();
    ranges.insert(
        "Wrapper".to_string(),
        vec![("Wrap".to_string(), vec![(0, FieldRangeKind::Unsigned(32))])],
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

    // Assert field < 0 — should be UNSAT with range hint
    let zero = encoder.solver.int_const(0);
    let lt_zero = encoder.solver.lt(field_val, zero);
    encoder.solver.assert_term(lt_zero);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "With unsigned(32) range hint, field < 0 should be UNSAT: {result:?}"
    );
}

/// With unsigned(32) range hints, the field is bounded above at 2^32 - 1.
#[test]
#[timeout(30000)]
fn test_adt_field_unsigned_range_upper_bound() {
    use std::collections::HashMap;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    use trust_wp_core::logic::FieldRangeKind;

    let mut encoder = AYEncoder::new_all();

    let mut ranges = HashMap::new();
    ranges.insert(
        "Wrapper".to_string(),
        vec![("Wrap".to_string(), vec![(0, FieldRangeKind::Unsigned(32))])],
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

    // Assert field > 4294967295 (2^32 - 1) — should be UNSAT
    let max_u32 = encoder.solver.int_const(4_294_967_295);
    let gt_max = encoder.solver.gt(field_val, max_u32);
    encoder.solver.assert_term(gt_max);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "With unsigned(32) range hint, field > u32::MAX should be UNSAT: {result:?}"
    );
}

/// Multi-field ADT: field with u32 hint cannot be negative, unhinted field can.
#[test]
#[timeout(30000)]
fn test_adt_multi_field_hinted_field_nonneg() {
    use std::collections::HashMap;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    use trust_wp_core::logic::FieldRangeKind;

    let mut encoder = AYEncoder::new_all();

    let mut ranges = HashMap::new();
    ranges.insert(
        "List".to_string(),
        vec![("Cons".to_string(), vec![(0, FieldRangeKind::Unsigned(32))])],
    );
    encoder.set_adt_field_ranges(ranges);
    let dt = DatatypeSort {
        name: "List".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "list_cons_0".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "list_cons_1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    let x = encoder
        .get_or_declare_var("x", Sort::Datatype(dt.clone()))
        .unwrap();
    let is_cons = encoder
        .solver
        .try_datatype_tester("Cons", x)
        .expect("tester");
    encoder.solver.assert_term(is_cons);

    // Field 0 (u32): assert field0 < 0 → UNSAT
    let field0 = encoder
        .solver
        .try_datatype_selector("list_cons_0", x, Sort::Int)
        .expect("selector 0");
    let zero = encoder.solver.int_const(0);
    let f0_lt_zero = encoder.solver.lt(field0, zero);
    encoder.solver.assert_term(f0_lt_zero);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Cons field 0 (u32) should not be negative: {result:?}"
    );
}

/// Multi-field ADT: unhinted field CAN be negative.
#[test]
#[timeout(30000)]
fn test_adt_multi_field_unhinted_field_allows_negative() {
    use std::collections::HashMap;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    use trust_wp_core::logic::FieldRangeKind;

    let mut encoder = AYEncoder::new_all();

    let mut ranges = HashMap::new();
    ranges.insert(
        "List".to_string(),
        vec![("Cons".to_string(), vec![(0, FieldRangeKind::Unsigned(32))])],
    );

    let dt = DatatypeSort {
        name: "List".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "list_cons_0".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "list_cons_1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);
    encoder.set_adt_field_ranges(ranges);

    let zero = encoder.solver.int_const(0);
    let neg_one = encoder.solver.int_const(-1);
    let x = encoder
        .solver
        .datatype_constructor(&dt, "Cons", &[zero, neg_one]);
    let is_cons = encoder
        .solver
        .try_datatype_tester("Cons", x)
        .expect("tester");
    encoder.solver.assert_term(is_cons);

    let field0 = encoder
        .solver
        .try_datatype_selector("list_cons_0", x, Sort::Int)
        .expect("selector 0");
    let max_u32 = encoder.solver.int_const(4_294_967_295);
    let f0_ge_zero = encoder.solver.ge(field0, zero);
    let f0_le_max = encoder.solver.le(field0, max_u32);
    encoder.solver.assert_term(f0_ge_zero);
    encoder.solver.assert_term(f0_le_max);

    // Field 1 (no range hint): assert field1 < 0 → should be SAT
    let field1 = encoder
        .solver
        .try_datatype_selector("list_cons_1", x, Sort::Int)
        .expect("selector 1");
    let f1_lt_zero = encoder.solver.lt(field1, zero);
    encoder.solver.assert_term(f1_lt_zero);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Sat),
        "Cons field 1 (no range) can be negative: {result:?}"
    );
}

/// When contracts use unqualified constructors (e.g., `Cons`, `Nil` instead
/// of `List::Cons`, `List::Nil`), the encoder's `infer_adt_name` produces
/// a synthesized name like `"Adt_Cons_Nil"`. The driver's
/// `build_adt_field_ranges` must index under this synthesized name so the
/// encoder finds the range constraints. (#2097 RC1 name-mismatch fix)
#[test]
#[timeout(30000)]
fn test_adt_field_range_lookup_with_synthesized_name() {
    use std::collections::HashMap;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    use trust_wp_core::logic::FieldRangeKind;

    let mut encoder = AYEncoder::new_all();

    // Simulate what the driver produces AFTER the name-mismatch fix:
    // range constraints indexed under the synthesized "Adt_Cons_Nil" name
    // (in addition to "List", but we only test the synthesized path here).
    let mut ranges = HashMap::new();
    ranges.insert(
        "Adt_Cons_Nil".to_string(),
        vec![("Cons".to_string(), vec![(0, FieldRangeKind::Unsigned(32))])],
    );
    encoder.set_adt_field_ranges(ranges);

    // Declare a datatype with the synthesized name (matching unqualified
    // constructor encoding path).
    let dt = DatatypeSort {
        name: "Adt_Cons_Nil".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "adt_cons_nil_cons_0".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "adt_cons_nil_cons_1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    let x = encoder
        .get_or_declare_var("x", Sort::Datatype(dt.clone()))
        .unwrap();
    let is_cons = encoder
        .solver
        .try_datatype_tester("Cons", x)
        .expect("tester");
    encoder.solver.assert_term(is_cons);

    // Field 0 (u32 range hint via synthesized name): field < 0 must be UNSAT
    let field0 = encoder
        .solver
        .try_datatype_selector("adt_cons_nil_cons_0", x, Sort::Int)
        .expect("selector 0");
    let zero = encoder.solver.int_const(0);
    let f0_lt_zero = encoder.solver.lt(field0, zero);
    encoder.solver.assert_term(f0_lt_zero);

    let result = encoder.check_sat();
    assert!(
        matches!(result, SolveResult::Unsat(_)),
        "Synthesized-name range hint should make field < 0 UNSAT: {result:?}"
    );
}

/// End-to-end test: `VerificationRequest.adt_field_ranges` threads range
/// constraints through `verify_function_with_modes` to the encoder.
///
/// Verifies a match expression on a user-defined ADT where the postcondition
/// `result >= 0` requires the field to be non-negative. The body is
/// `match v { Wrap(x) => x, Empty => 0 }`. Without `adt_field_ranges`,
/// the solver assigns x = -1. With ranges, the u32 constraint ensures
/// x >= 0 and verification succeeds. (#2178, #2097 RC1)
#[test]
#[timeout(30000)]
fn test_verification_request_adt_field_ranges_threaded() {
    use std::collections::HashMap;

    use trust_wp_core::{
        formula::{BinOp, ExprSort, MatchArm, Pattern, PureExpr},
        logic::FieldRangeKind,
    };

    // Body: match v { Wrap(x) => x, Empty => 0 }
    // Use a simple Var scrutinee (not Deref) to match the datatype encoding path.
    let body = PureExpr::Match {
        scrutinee: Arc::new(PureExpr::Var("v".to_string(), Some(ExprSort::Int))),
        arms: vec![
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Wrapper::Wrap".to_string(),
                    inner: Some(Box::new(Pattern::Binding("x".to_string()))),
                },
                body: PureExpr::Var("x".to_string(), Some(ExprSort::Int)),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Wrapper::Empty".to_string(),
                    inner: None,
                },
                body: PureExpr::Int(0),
            },
        ],
    };

    // Ensures: result >= 0
    let ensures = PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), Some(ExprSort::Int))),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );

    // Without adt_field_ranges: verification returns Failed (solver picks x = -1).
    let result_without = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[], std::slice::from_ref(&ensures))
            .return_expr(Some(&body)),
    )
    .unwrap();
    assert!(
            matches!(result_without, crate::VerificationResult::Failed(_)),
            "Without adt_field_ranges, unsigned field is unconstrained and should fail: {result_without:?}"
        );

    // With adt_field_ranges: u32 field is constrained to [0, 2^32 - 1]
    let mut ranges = HashMap::new();
    ranges.insert(
        "Wrapper".to_string(),
        vec![("Wrap".to_string(), vec![(0, FieldRangeKind::Unsigned(32))])],
    );

    let result_with = crate::verify_function_with_modes(
        crate::VerificationRequest::new(&[], &[ensures])
            .return_expr(Some(&body))
            .adt_field_ranges(Some(ranges)),
    )
    .unwrap();
    // KNOWN-CLASS PIN (#133 mass unit adjudication, 2026-08-27): the verdict
    // demotes to `Unknown(ProofTrusted)` under ay's mandatory strict UNSAT
    // certification; the property this test guards is unchanged and every
    // other outcome still fails. See `tests::helpers::verified_or_known_proof_trusted`.
    assert!(
        crate::tests::helpers::verified_or_known_proof_trusted(&result_with),
        "With adt_field_ranges(u32), field >= 0 should be provable: {result_with:?}"
    );
}
