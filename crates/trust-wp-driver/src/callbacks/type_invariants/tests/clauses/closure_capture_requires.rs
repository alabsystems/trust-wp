// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// --- Closure capture type invariant requires tests (#2257) ---

fn make_test_invariant(type_name: &str) -> trust_wp_core::logic::TypeInvariantDef {
    make_test_invariant_with_body(type_name, PureExpr::Bool(true))
}

fn make_test_invariant_with_body(
    type_name: &str,
    body: PureExpr,
) -> trust_wp_core::logic::TypeInvariantDef {
    trust_wp_core::type_invariant_def! {
        type_name: type_name.to_string(),
        self_param: "self".to_string(),
        param_sort: None,
        body: body,
        is_newtype: false,
        element_invariant_method: None,
    }
}

#[test]
fn closure_capture_invariant_empty_inputs_returns_empty() {
    let result = build_closure_capture_invariant_requires(&[], &[]);
    assert!(result.is_empty());

    let inv = make_test_invariant("Zero");
    let result = build_closure_capture_invariant_requires(&[], &[inv]);
    assert!(result.is_empty());
}

#[test]
fn closure_capture_invariant_no_matching_type_returns_empty() {
    let inv = make_test_invariant_with_body(
        "OtherType",
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".into(), None)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(0)),
        ),
    );
    let unrelated_id = intern_sort_name("UnrelatedType");
    let capture = CaptureField::new("x", ExprSort::Datatype(unrelated_id), CaptureKind::ByValue);
    let info = ClosureCaptureInfo::new("test::closure#0".into(), vec![capture]);

    let result = build_closure_capture_invariant_requires(&[info], &[inv]);
    assert!(
        result.is_empty(),
        "no matching type should produce no requires"
    );
}

#[test]
fn closure_capture_invariant_trivial_body_skipped() {
    let inv = make_test_invariant("TrivialType");
    let trivial_id = intern_sort_name("TrivialType");
    let capture = CaptureField::new("x", ExprSort::Datatype(trivial_id), CaptureKind::ByValue);
    let info = ClosureCaptureInfo::new("test::trivial#0".into(), vec![capture]);

    let result = build_closure_capture_invariant_requires(&[info], &[inv]);
    assert!(
        result.is_empty(),
        "trivial invariant (body=true) should be skipped"
    );
}

#[test]
fn closure_capture_invariant_matching_type_emits_method_call() {
    let zero_id = intern_sort_name("Zero");
    let inv = make_test_invariant_with_body(
        "Zero",
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        ),
    );
    let capture = CaptureField::new("x", ExprSort::Datatype(zero_id), CaptureKind::ByValue);
    let info = ClosureCaptureInfo::new("test::closure_zero#0".into(), vec![capture]);

    let result = build_closure_capture_invariant_requires(&[info], &[inv]);
    assert_eq!(result.len(), 1, "should emit one requires clause");
    match &result[0] {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            assert!(
                method.contains("Zero"),
                "method should reference Zero, got {method}"
            );
            assert!(args.is_empty());
            assert!(
                matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "x"),
                "receiver should be Var(x), got {receiver:?}"
            );
        }
        other => panic!("expected MethodCall, got {other:?}"),
    }
}

#[test]
fn closure_capture_invariant_ref_wrapper_peeled() {
    let zero_id = intern_sort_name("Zero");
    let inv = make_test_invariant_with_body(
        "Zero",
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        ),
    );
    let capture = CaptureField::new(
        "x",
        ExprSort::Ref(Box::new(ExprSort::Datatype(zero_id))),
        CaptureKind::ByRef,
    );
    let info = ClosureCaptureInfo::new("test::ref_closure#0".into(), vec![capture]);

    let result = build_closure_capture_invariant_requires(&[info], &[inv]);
    assert_eq!(result.len(), 1, "Ref wrapper should be peeled to find type");
}

#[test]
fn closure_capture_invariant_mut_ref_wrapper_peeled() {
    let zero_id = intern_sort_name("Zero");
    let inv = make_test_invariant_with_body(
        "Zero",
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        ),
    );
    let capture = CaptureField::new(
        "x",
        ExprSort::MutRef(Box::new(ExprSort::Datatype(zero_id))),
        CaptureKind::ByMutRef,
    );
    let info = ClosureCaptureInfo::new("test::mutref_closure#0".into(), vec![capture]);

    let result = build_closure_capture_invariant_requires(&[info], &[inv]);
    assert_eq!(
        result.len(),
        1,
        "MutRef wrapper should be peeled to find type"
    );
}

#[test]
fn closure_capture_invariant_int_sort_returns_none() {
    let inv = make_test_invariant_with_body(
        "Zero",
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        ),
    );
    let capture = CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue);
    let info = ClosureCaptureInfo::new("test::int_closure#0".into(), vec![capture]);

    let result = build_closure_capture_invariant_requires(&[info], &[inv]);
    assert!(result.is_empty(), "Int sort should not match any invariant");
}

#[test]
fn closure_capture_invariant_deduplicates_across_closures() {
    let zero_id = intern_sort_name("Zero");
    let inv = make_test_invariant_with_body(
        "Zero",
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        ),
    );
    let capture1 = CaptureField::new("x", ExprSort::Datatype(zero_id), CaptureKind::ByValue);
    let capture2 = CaptureField::new("x", ExprSort::Datatype(zero_id), CaptureKind::ByValue);
    let info1 = ClosureCaptureInfo::new("test::closure1#0".into(), vec![capture1]);
    let info2 = ClosureCaptureInfo::new("test::closure2#0".into(), vec![capture2]);

    let result = build_closure_capture_invariant_requires(&[info1, info2], &[inv]);
    assert_eq!(
        result.len(),
        1,
        "same capture x+Zero across closures should deduplicate"
    );
}

#[test]
fn current_closure_self_invariant_uses_self_projection_receiver() {
    let zero_id = intern_sort_name("Zero");
    let inv = make_test_invariant_with_body(
        "Zero",
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("self".into(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(0)),
        ),
    );
    let capture = CaptureField::new("x", ExprSort::Datatype(zero_id), CaptureKind::ByValue);
    let info = ClosureCaptureInfo::new("test::closure#0".into(), vec![capture])
        .with_param_name(Some("self".to_string()));

    let result = build_current_closure_self_invariant_requires(&[info], &[inv]);
    assert_eq!(
        result.len(),
        1,
        "current closure should get one self-field invariant requires clause"
    );
    match &result[0] {
        PureExpr::MethodCall { receiver, .. } => {
            assert!(
                matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "self.0"),
                "receiver should use the current closure's self-field projection, got {receiver:?}"
            );
        }
        other => panic!("expected MethodCall, got {other:?}"),
    }
}
