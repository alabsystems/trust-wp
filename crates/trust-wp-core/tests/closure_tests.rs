// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integration tests for `ClosureCaptureInfo` and `CaptureField`.

use trust_wp_core::{
    closure::{CaptureField, CaptureKind, ClosureCaptureInfo},
    formula::{ExprSort, PureExpr},
};

// ── CaptureKind ──────────────────────────────────────────────────

#[test]
fn capture_kind_eq() {
    assert_eq!(CaptureKind::ByValue, CaptureKind::ByValue);
    assert_eq!(CaptureKind::ByRef, CaptureKind::ByRef);
    assert_eq!(CaptureKind::ByMutRef, CaptureKind::ByMutRef);
}

#[test]
fn capture_kind_ne() {
    assert_ne!(CaptureKind::ByValue, CaptureKind::ByRef);
    assert_ne!(CaptureKind::ByRef, CaptureKind::ByMutRef);
    assert_ne!(CaptureKind::ByValue, CaptureKind::ByMutRef);
}

#[test]
fn capture_kind_debug() {
    let dbg = format!("{:?}", CaptureKind::ByMutRef);
    assert!(
        dbg.contains("ByMutRef"),
        "Debug should contain variant name"
    );
}

#[test]
fn capture_kind_copy() {
    let k = CaptureKind::ByValue;
    let k2 = k;
    assert_eq!(k, k2);
}

// ── CaptureField ─────────────────────────────────────────────────

#[test]
fn capture_field_accessors() {
    let field = CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue);
    assert_eq!(field.name(), "x");
    assert_eq!(*field.sort(), ExprSort::Int);
    assert_eq!(field.kind(), CaptureKind::ByValue);
}

#[test]
fn capture_field_with_seq_sort() {
    let field = CaptureField::new("items", ExprSort::Seq, CaptureKind::ByMutRef);
    assert_eq!(field.name(), "items");
    assert_eq!(*field.sort(), ExprSort::Seq);
    assert_eq!(field.kind(), CaptureKind::ByMutRef);
}

#[test]
fn capture_field_with_bool_sort_by_ref() {
    let field = CaptureField::new("flag", ExprSort::Bool, CaptureKind::ByRef);
    assert_eq!(field.name(), "flag");
    assert_eq!(*field.sort(), ExprSort::Bool);
    assert_eq!(field.kind(), CaptureKind::ByRef);
}

#[test]
fn capture_field_equality() {
    let a = CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue);
    let b = CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue);
    assert_eq!(a, b);
}

#[test]
fn capture_field_inequality_name() {
    let a = CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue);
    let b = CaptureField::new("y", ExprSort::Int, CaptureKind::ByValue);
    assert_ne!(a, b);
}

#[test]
fn capture_field_inequality_sort() {
    let a = CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue);
    let b = CaptureField::new("x", ExprSort::Bool, CaptureKind::ByValue);
    assert_ne!(a, b);
}

#[test]
fn capture_field_inequality_kind() {
    let a = CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue);
    let b = CaptureField::new("x", ExprSort::Int, CaptureKind::ByRef);
    assert_ne!(a, b);
}

#[test]
fn capture_field_clone() {
    let a = CaptureField::new("x", ExprSort::Int, CaptureKind::ByMutRef);
    let b = a.clone();
    assert_eq!(a, b);
}

#[test]
fn capture_field_name_from_string() {
    let field = CaptureField::new(String::from("dynamic"), ExprSort::Int, CaptureKind::ByValue);
    assert_eq!(field.name(), "dynamic");
}

// ── ClosureCaptureInfo ───────────────────────────────────────────

#[test]
fn closure_capture_info_new_defaults() {
    let info = ClosureCaptureInfo::new("my::closure".to_string(), vec![]);
    assert_eq!(info.def_id(), "my::closure");
    assert!(info.captures().is_empty());
    assert_eq!(info.param_name(), None);
    assert_eq!(info.body_expr(), None);
    assert_eq!(info.param_names(), None);
    assert_eq!(info.ensures_exprs(), None);
}

#[test]
fn closure_capture_info_with_captures() {
    let fields = vec![
        CaptureField::new("x", ExprSort::Int, CaptureKind::ByValue),
        CaptureField::new("y", ExprSort::Bool, CaptureKind::ByRef),
    ];
    let info = ClosureCaptureInfo::new("test::closure".to_string(), fields);
    assert_eq!(info.captures().len(), 2);
    assert_eq!(info.captures()[0].name(), "x");
    assert_eq!(info.captures()[1].name(), "y");
}

#[test]
fn closure_capture_info_with_param_name() {
    let info = ClosureCaptureInfo::new("c".to_string(), vec![])
        .with_param_name(Some("my_closure".to_string()));
    assert_eq!(info.param_name(), Some("my_closure"));
}

#[test]
fn closure_capture_info_param_name_none() {
    let info = ClosureCaptureInfo::new("c".to_string(), vec![]).with_param_name(None);
    assert_eq!(info.param_name(), None);
}

#[test]
fn closure_capture_info_with_body_expr() {
    let body = PureExpr::Int(42);
    let info = ClosureCaptureInfo::new("c".to_string(), vec![]).with_body_expr(Some(body.clone()));
    assert_eq!(info.body_expr(), Some(&body));
}

#[test]
fn closure_capture_info_body_expr_none() {
    let info = ClosureCaptureInfo::new("c".to_string(), vec![]).with_body_expr(None);
    assert_eq!(info.body_expr(), None);
}

#[test]
fn closure_capture_info_with_param_names() {
    let info = ClosureCaptureInfo::new("c".to_string(), vec![])
        .with_param_names(Some(vec!["x".to_string(), "y".to_string()]));
    let names = info.param_names().unwrap();
    assert_eq!(names, &["x", "y"]);
}

#[test]
fn closure_capture_info_with_ensures_exprs() {
    let ensures = vec![PureExpr::Bool(true)];
    let info =
        ClosureCaptureInfo::new("c".to_string(), vec![]).with_ensures_exprs(Some(ensures.clone()));
    assert_eq!(info.ensures_exprs(), Some(ensures.as_slice()));
}

#[test]
fn closure_capture_info_builder_chain() {
    let body = PureExpr::Int(1);
    let info = ClosureCaptureInfo::new(
        "test::full".to_string(),
        vec![CaptureField::new("x", ExprSort::Int, CaptureKind::ByMutRef)],
    )
    .with_param_name(Some("f".to_string()))
    .with_body_expr(Some(body.clone()))
    .with_param_names(Some(vec!["arg".to_string()]))
    .with_ensures_exprs(Some(vec![PureExpr::Bool(true)]));

    assert_eq!(info.def_id(), "test::full");
    assert_eq!(info.captures().len(), 1);
    assert_eq!(info.param_name(), Some("f"));
    assert_eq!(info.body_expr(), Some(&body));
    assert_eq!(info.param_names().unwrap(), &["arg"]);
    assert_eq!(info.ensures_exprs().unwrap().len(), 1);
}

#[test]
fn closure_capture_info_overwrite_optional() {
    let info = ClosureCaptureInfo::new("c".to_string(), vec![])
        .with_param_name(Some("first".to_string()))
        .with_param_name(Some("second".to_string()));
    assert_eq!(info.param_name(), Some("second"));
}
