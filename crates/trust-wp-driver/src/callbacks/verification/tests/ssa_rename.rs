// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, PureExpr};

use crate::callbacks::verification::contract_transform::ssa_rename_call_assumptions;

#[test]
fn ssa_rename_noop_for_single_mutation() {
    let mut assumptions = vec![PureExpr::BinOp(
        Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "v".to_string(),
            None,
        )))),
        BinOp::Eq,
        Arc::new(PureExpr::Int(42)),
    )];
    let changed = ssa_rename_call_assumptions(&mut assumptions);
    assert!(!changed, "single Final depth should not trigger SSA rename");
}

#[test]
fn ssa_rename_two_sequential_mutations() {
    let mut assumptions = vec![
        PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
                "v".to_string(),
                None,
            )))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        ),
        PureExpr::BinOp(
            Arc::new(PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(
                PureExpr::Var("v".to_string(), None),
            ))))),
            BinOp::Eq,
            Arc::new(PureExpr::Int(1)),
        ),
    ];
    let changed = ssa_rename_call_assumptions(&mut assumptions);
    assert!(changed, "depth 2 should trigger SSA rename");
    match &assumptions[0] {
        PureExpr::BinOp(lhs, BinOp::Eq, _) => match lhs.as_ref() {
            PureExpr::Var(name, _) => assert_eq!(name, "v_ssa_1"),
            other => panic!("expected Var(v_ssa_1), got {other:?}"),
        },
        other => panic!("expected BinOp, got {other:?}"),
    }
    match &assumptions[1] {
        PureExpr::BinOp(lhs, BinOp::Eq, _) => match lhs.as_ref() {
            PureExpr::Final(inner) => match inner.as_ref() {
                PureExpr::Var(name, _) => assert_eq!(name, "v"),
                other => panic!("expected Var(v), got {other:?}"),
            },
            other => panic!("expected Final(Var(v)), got {other:?}"),
        },
        other => panic!("expected BinOp, got {other:?}"),
    }
}

#[test]
fn ssa_rename_three_sequential_mutations() {
    let mut assumptions = vec![
        PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None))),
        PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        ))))),
        PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::Final(
            Arc::new(PureExpr::Var("x".to_string(), None)),
        ))))),
    ];
    let changed = ssa_rename_call_assumptions(&mut assumptions);
    assert!(changed);
    assert!(matches!(&assumptions[0], PureExpr::Var(n, _) if n == "x_ssa_1"));
    assert!(matches!(&assumptions[1], PureExpr::Var(n, _) if n == "x_ssa_2"));
    assert!(
        matches!(&assumptions[2], PureExpr::Final(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "x"))
    );
}

#[test]
fn ssa_rename_preserves_deref_base() {
    let mut assumptions = vec![
        PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        ))))),
        PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::Deref(
            Arc::new(PureExpr::Var("x".to_string(), None)),
        ))))),
    ];
    let changed = ssa_rename_call_assumptions(&mut assumptions);
    assert!(changed);
    match &assumptions[0] {
        PureExpr::Deref(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => assert_eq!(name, "x_ssa_1"),
            other => panic!("expected Var(x_ssa_1), got {other:?}"),
        },
        other => panic!("expected Deref, got {other:?}"),
    }
    match &assumptions[1] {
        PureExpr::Final(inner) => match inner.as_ref() {
            PureExpr::Deref(inner2) => match inner2.as_ref() {
                PureExpr::Var(name, _) => assert_eq!(name, "x"),
                other => panic!("expected Var(x), got {other:?}"),
            },
            other => panic!("expected Deref(Var(x)), got {other:?}"),
        },
        other => panic!("expected Final, got {other:?}"),
    }
}

#[test]
fn ssa_rename_empty_assumptions_is_noop() {
    let mut assumptions = vec![];
    let changed = ssa_rename_call_assumptions(&mut assumptions);
    assert!(!changed, "empty input should return false");
}

#[test]
fn ssa_rename_mixed_variables_independent() {
    // v has depth 2 (should be renamed), w has depth 1 (should be untouched).
    let mut assumptions = vec![
        // v depth 1: Final(Var("v"))
        PureExpr::Final(Arc::new(PureExpr::Var("v".to_string(), None))),
        // v depth 2: Final(Final(Var("v")))
        PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "v".to_string(),
            None,
        ))))),
        // w depth 1: Final(Var("w")) -- only single depth, no rename
        PureExpr::Final(Arc::new(PureExpr::Var("w".to_string(), None))),
    ];
    let changed = ssa_rename_call_assumptions(&mut assumptions);
    assert!(changed, "v at depth 2 should trigger rename");

    // v depth 1 -> v_ssa_1 (intermediate)
    assert!(
        matches!(&assumptions[0], PureExpr::Var(n, _) if n == "v_ssa_1"),
        "v depth-1 should become v_ssa_1, got {:?}",
        assumptions[0]
    );
    // v depth 2 -> Final(Var("v")) (max depth collapse)
    assert!(
        matches!(&assumptions[1], PureExpr::Final(inner)
            if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "v")),
        "v depth-2 should collapse to Final(Var(v)), got {:?}",
        assumptions[1]
    );
    // w depth 1 -> unchanged (w is not a rename target)
    assert!(
        matches!(&assumptions[2], PureExpr::Final(inner)
            if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "w")),
        "w should remain Final(Var(w)), got {:?}",
        assumptions[2]
    );
}

/// Regression: ContinueWithAssumptions phase isolation (#2361).
///
/// The driver takes a pre-loop unsoundness snapshot and restores it when
/// the loop path returns ContinueWithAssumptions. This test verifies:
/// 1. Pre-loop driver increments survive the restore (OpaqueCallTrueAssumption)
/// 2. Loop-only increments are erased (SortFallbackToInt)
#[test]
fn test_continue_with_assumptions_unsoundness_phase_isolation() {
    use trust_wp_ay::unsoundness::{self, UnsoundnessCategory};

    unsoundness::reset();

    // 1. Take driver baseline (before any increments).
    let driver_before = unsoundness::snapshot();

    // 2. Simulate a driver-side increment from parse/MIR extraction.
    unsoundness::increment(UnsoundnessCategory::OpaqueCallTrueAssumption);

    // 3. Take pre-loop snapshot (what verification.rs now does before verify_contract_loop_path).
    let pre_loop_snapshot = unsoundness::snapshot();

    // 4. Simulate loop-phase increments (init/preservation/postcondition sub-checks).
    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
    unsoundness::increment(UnsoundnessCategory::SortFallbackToInt);
    unsoundness::increment(UnsoundnessCategory::ClosureBodyTrueDefault);

    // Verify loop increments are visible before restore.
    let during_loop = unsoundness::snapshot();
    assert_eq!(
        during_loop.get(&UnsoundnessCategory::SortFallbackToInt),
        Some(&2),
        "loop-phase SortFallbackToInt should be visible before restore"
    );

    // 5. Restore to pre-loop snapshot (ContinueWithAssumptions path).
    unsoundness::restore(&pre_loop_snapshot);

    // 6. Verify: driver-side increment survived.
    let after_restore = unsoundness::snapshot();
    let function_delta = unsoundness::delta(&driver_before, &after_restore);
    assert_eq!(
        function_delta.get(&UnsoundnessCategory::OpaqueCallTrueAssumption),
        Some(&1),
        "pre-loop driver increment must survive phase restore"
    );

    // 7. Verify: loop-only increments are gone.
    assert_eq!(
        after_restore.get(&UnsoundnessCategory::SortFallbackToInt),
        None,
        "loop-phase SortFallbackToInt must be erased by restore"
    );
    assert_eq!(
        after_restore.get(&UnsoundnessCategory::ClosureBodyTrueDefault),
        None,
        "loop-phase ClosureBodyTrueDefault must be erased by restore"
    );

    // 8. Verify the delta from driver_before contains ONLY the driver increment.
    assert_eq!(
        function_delta.len(),
        1,
        "function-level delta should contain only pre-loop driver increments, got: {:?}",
        function_delta
    );

    unsoundness::reset();
}
