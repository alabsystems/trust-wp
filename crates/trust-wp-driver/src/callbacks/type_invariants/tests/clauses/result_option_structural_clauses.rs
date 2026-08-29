// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{
    super::common::{
        collect_type_invariant_clauses, collect_type_invariant_clauses_with_invariants, find_arm,
        rewrite_inv_from_source,
    },
    *,
};

#[test]
fn enum_result_param_generates_structural_match_precondition() {
    let source = r#"
#[allow(dead_code)]
pub struct NonZero(i32);

#[allow(dead_code)]
pub struct Sum10(i32, i32);

pub fn takes_result(x: Result<NonZero, Sum10>) {
let _ = x;
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses_with_invariants(
        source,
        "takes_result",
        &["x"],
        &["NonZero", "Sum10"],
    );
    assert_eq!(reqs.len(), 1, "expected one structural match precondition");
    assert!(
        enss.is_empty(),
        "by-value enum param should not add ensures"
    );

    let PureExpr::Match { scrutinee, arms } = &reqs[0] else {
        panic!("expected Match precondition, got {:?}", reqs[0]);
    };
    assert!(
        matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "x"),
        "expected match scrutinee to be x, got {scrutinee:?}"
    );
    assert_eq!(arms.len(), 2, "Result should produce Ok/Err arms");

    let ok_arm = find_arm(arms, "Ok");
    let Pattern::Constructor {
        inner: Some(inner), ..
    } = &ok_arm.pattern
    else {
        panic!("Ok arm should bind its payload: {:?}", ok_arm.pattern);
    };
    let Pattern::Binding(binding_name) = inner.as_ref() else {
        panic!("Ok arm should use a binding pattern, got {inner:?}");
    };
    assert!(
        matches!(
            &ok_arm.body,
            PureExpr::MethodCall { receiver, method, .. }
                if method.contains("NonZero")
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == binding_name)
        ),
        "Ok arm should call NonZero invariant on bound payload, got {:?}",
        ok_arm.body
    );

    let err_arm = find_arm(arms, "Err");
    let Pattern::Constructor {
        inner: Some(inner), ..
    } = &err_arm.pattern
    else {
        panic!("Err arm should bind its payload: {:?}", err_arm.pattern);
    };
    let Pattern::Binding(binding_name) = inner.as_ref() else {
        panic!("Err arm should use a binding pattern, got {inner:?}");
    };
    assert!(
        matches!(
            &err_arm.body,
            PureExpr::MethodCall { receiver, method, .. }
                if method.contains("Sum10")
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == binding_name)
        ),
        "Err arm should call Sum10 invariant on bound payload, got {:?}",
        err_arm.body
    );
}

#[test]
fn option_param_generates_some_payload_and_none_true_arms() {
    let source = r#"
#[allow(dead_code)]
pub struct NonZero(i32);

pub fn takes_option(x: Option<NonZero>) {
let _ = x;
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses_with_invariants(
        source,
        "takes_option",
        &["x"],
        &["NonZero"],
    );
    assert_eq!(reqs.len(), 1, "expected one structural match precondition");
    assert!(
        enss.is_empty(),
        "by-value option param should not add ensures"
    );

    let PureExpr::Match { arms, .. } = &reqs[0] else {
        panic!("expected Match precondition, got {:?}", reqs[0]);
    };

    let some_arm = find_arm(arms, "Some");
    let Pattern::Constructor {
        inner: Some(inner), ..
    } = &some_arm.pattern
    else {
        panic!("Some arm should bind its payload: {:?}", some_arm.pattern);
    };
    let Pattern::Binding(binding_name) = inner.as_ref() else {
        panic!("Some arm should use a binding pattern, got {inner:?}");
    };
    assert!(
        matches!(
            &some_arm.body,
            PureExpr::MethodCall { receiver, method, .. }
                if method.contains("NonZero")
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == binding_name)
        ),
        "Some arm should call NonZero invariant on bound payload, got {:?}",
        some_arm.body
    );

    let none_arm = find_arm(arms, "None");
    assert!(
        matches!(none_arm.body, PureExpr::Bool(true)),
        "None arm should be trivially true, got {:?}",
        none_arm.body
    );
}

#[test]
fn generated_structural_param_invariant_recurses_through_nested_enum_and_tuple() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

#[allow(dead_code)]
pub enum Foo<'a, T> {
    A { f1: &'a mut Sum10, f2: usize },
    B(T),
}

pub fn use_foo<'a>(x: Foo<'a, (Foo<'a, u32>, &'a mut Sum10)>) {
let _ = x;
}
"#;
    let (reqs, enss) =
        collect_type_invariant_clauses_with_invariants(source, "use_foo", &["x"], &["Sum10"]);
    assert_eq!(
        reqs.len(),
        1,
        "nested structural enum param should produce one requires clause"
    );
    assert!(
        enss.is_empty(),
        "by-value nested structural enum param should not add ensures"
    );

    let PureExpr::Match { scrutinee, arms } = &reqs[0] else {
        panic!("expected top-level Match precondition, got {:?}", reqs[0]);
    };
    assert!(
        matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "x"),
        "expected top-level match scrutinee x, got {scrutinee:?}"
    );
    assert_eq!(arms.len(), 2, "Foo should produce A/B match arms");

    let a_arm = find_arm(arms, "A");
    let Pattern::Constructor {
        inner: Some(inner), ..
    } = &a_arm.pattern
    else {
        panic!("A arm should bind its fields: {:?}", a_arm.pattern);
    };
    let Pattern::Tuple(fields) = inner.as_ref() else {
        panic!("A arm should use a tuple-style field pattern, got {inner:?}");
    };
    assert_eq!(fields.len(), 2, "A arm should bind both fields");
    let Pattern::Binding(f1_binding) = &fields[0] else {
        panic!("A.f1 should bind its field, got {:?}", fields[0]);
    };
    assert!(
        matches!(
            &a_arm.body,
            PureExpr::MethodCall { receiver, method, .. }
                if method.contains("Sum10")
                    && matches!(
                        receiver.as_ref(),
                        PureExpr::Deref(inner)
                            if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == f1_binding)
                    )
        ),
        "A arm should require inv(*f1), got {:?}",
        a_arm.body
    );

    let b_arm = find_arm(arms, "B");
    let Pattern::Constructor {
        inner: Some(inner), ..
    } = &b_arm.pattern
    else {
        panic!("B arm should bind its payload: {:?}", b_arm.pattern);
    };
    let Pattern::Binding(binding_name) = inner.as_ref() else {
        panic!("B arm should bind its tuple payload, got {inner:?}");
    };
    let PureExpr::BinOp(lhs, BinOp::And, rhs) = &b_arm.body else {
        panic!(
            "B arm should conjoin nested Foo and Sum10 invariants, got {:?}",
            b_arm.body
        );
    };
    let PureExpr::Match {
        scrutinee: nested_scrutinee,
        arms: nested_arms,
    } = lhs.as_ref()
    else {
        panic!(
            "B arm lhs should recursively match on tuple field 0, got {:?}",
            lhs
        );
    };
    assert!(
        matches!(
            nested_scrutinee.as_ref(),
            PureExpr::LogicFnCall { name, args }
                if name.contains("tuple_get_0")
                    && matches!(&args[..], [PureExpr::Var(name, _)] if name == binding_name)
        ),
        "nested Foo recursion should project tuple field 0, got {nested_scrutinee:?}"
    );
    assert_eq!(
        nested_arms.len(),
        2,
        "nested Foo should also produce A/B arms"
    );
    assert!(
        matches!(&find_arm(nested_arms, "B").body, PureExpr::Bool(true)),
        "nested B(u32) arm should be trivial"
    );
    assert!(
        matches!(
            rhs.as_ref(),
            PureExpr::MethodCall { receiver, method, .. }
                if method.contains("Sum10")
                    && matches!(
                        receiver.as_ref(),
                        PureExpr::Deref(inner)
                            if matches!(
                                inner.as_ref(),
                                PureExpr::LogicFnCall { name, args }
                                    if name.contains("tuple_get_1")
                                        && matches!(&args[..], [PureExpr::Var(name, _)] if name == binding_name)
                            )
                    )
        ),
        "B arm rhs should require inv(tuple_get_1(payload)), got {:?}",
        rhs
    );
}

#[test]
fn rewrite_inv_for_nested_structural_enum_param_uses_match_expression() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

#[allow(dead_code)]
pub enum Foo<'a, T> {
    A { f1: &'a mut Sum10, f2: usize },
    B(T),
}

pub fn use_foo<'a>(x: Foo<'a, (Foo<'a, u32>, &'a mut Sum10)>) {
let _ = x;
}
"#;
    let rewritten = rewrite_inv_from_source(source, "use_foo", &["x"], &["Sum10"], "x");
    let (reqs, _) =
        collect_type_invariant_clauses_with_invariants(source, "use_foo", &["x"], &["Sum10"]);

    assert!(
        matches!(rewritten, PureExpr::Match { .. }),
        "inv(x) should rewrite to a structural match expression, got {rewritten:?}"
    );
    assert_eq!(
        reqs,
        vec![rewritten],
        "rewrite and clause generation should share the same structural expansion"
    );
}

#[test]
fn direct_result_return_generates_invariant_postcondition() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

pub fn returns_sum10() -> Sum10 {
panic!()
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses(source, "returns_sum10", &[]);
    assert!(
        reqs.is_empty(),
        "result-only function should have no requires"
    );
    assert_eq!(enss.len(), 1, "expected one direct result postcondition");
    assert!(
        matches!(
            &enss[0],
            PureExpr::MethodCall { receiver, method, args }
                if args.is_empty()
                    && method.contains("Sum10")
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "result")
        ),
        "direct result should produce an invariant call on `result`, got {:?}",
        enss[0]
    );
}

#[test]
fn open_inv_result_doc_marker_suppresses_direct_result_postcondition() {
    let source = r#"
#[allow(dead_code)]
pub struct Sum10(i32, i32);

#[doc = "trust-wp:open_inv_result:"]
pub fn returns_open_sum10() -> Sum10 {
panic!()
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses(source, "returns_open_sum10", &[]);
    assert!(
        reqs.is_empty(),
        "result-only function should have no requires"
    );
    assert!(
        enss.is_empty(),
        "open_inv_result doc marker should suppress the direct result invariant, got {enss:?}"
    );
}

#[test]
fn enum_result_return_generates_structural_match_postcondition() {
    let source = r#"
#[allow(dead_code)]
pub struct NonZero(i32);

#[allow(dead_code)]
pub struct Sum10(i32, i32);

pub fn returns_result() -> Result<NonZero, Sum10> {
panic!()
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses_with_invariants(
        source,
        "returns_result",
        &[],
        &["NonZero", "Sum10"],
    );
    assert!(
        reqs.is_empty(),
        "result-only function should have no requires"
    );
    assert_eq!(
        enss.len(),
        1,
        "expected one structural result postcondition"
    );

    let PureExpr::Match { scrutinee, arms } = &enss[0] else {
        panic!("expected Match ensure, got {:?}", enss[0]);
    };
    assert!(
        matches!(scrutinee.as_ref(), PureExpr::Var(name, _) if name == "result"),
        "expected result match scrutinee, got {scrutinee:?}"
    );
    assert_eq!(arms.len(), 2, "Result should produce Ok/Err arms");
    assert!(
        matches!(
            &find_arm(arms, "Ok").body,
            PureExpr::MethodCall { method, .. } if method.contains("NonZero")
        ),
        "Ok return arm should call NonZero invariant"
    );
    assert!(
        matches!(
            &find_arm(arms, "Err").body,
            PureExpr::MethodCall { method, .. } if method.contains("Sum10")
        ),
        "Err return arm should call Sum10 invariant"
    );
}

#[test]
fn open_inv_result_tool_attr_suppresses_structural_result_postcondition() {
    let source = r#"
#![feature(register_tool)]
#![register_tool(creusot)]

#[allow(dead_code)]
pub struct NonZero(i32);

#[allow(dead_code)]
pub struct Sum10(i32, i32);

#[creusot::open_inv_result]
pub fn returns_open_result() -> Result<NonZero, Sum10> {
panic!()
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses_with_invariants(
        source,
        "returns_open_result",
        &[],
        &["NonZero", "Sum10"],
    );
    assert!(
        reqs.is_empty(),
        "result-only function should have no requires"
    );
    assert!(
        enss.is_empty(),
        "creusot::open_inv_result should suppress the structural result invariant, got {enss:?}"
    );
}

#[test]
fn trivial_result_payloads_do_not_generate_structural_enum_clause() {
    let source = r#"
#[allow(dead_code)]
pub struct NonZero(i32);

pub fn trivial_result(x: Result<i32, i32>, y: NonZero) {
let _ = x;
let _ = y;
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses_with_invariants(
        source,
        "trivial_result",
        &["x", "y"],
        &["NonZero"],
    );
    assert_eq!(
        reqs.len(),
        1,
        "only the direct NonZero parameter should produce a clause, got {reqs:?}"
    );
    assert!(
        matches!(&reqs[0], PureExpr::MethodCall { receiver, method, .. }
            if method.contains("NonZero")
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "y")),
        "trivial Result payloads should not add a structural match clause, got {:?}",
        reqs[0]
    );
    assert!(enss.is_empty(), "no ensures expected for by-value params");
}

#[test]
fn mixed_supported_and_unsupported_enum_variants_fail_closed() {
    let source = r#"
#[allow(dead_code)]
pub struct NonZero(i32);

#[allow(dead_code)]
pub struct Wrapper(NonZero);

#[allow(dead_code)]
pub enum Mixed {
    One(NonZero),
    Two(Wrapper, i32),
}

pub fn takes_mixed(x: Mixed, y: NonZero) {
let _ = x;
let _ = y;
}
"#;
    let (reqs, enss) = collect_type_invariant_clauses_with_invariants(
        source,
        "takes_mixed",
        &["x", "y"],
        &["NonZero"],
    );
    assert!(
        matches!(&reqs[..], [PureExpr::MethodCall { receiver, method, .. }]
            if method.contains("NonZero")
                && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "y")),
        "unsupported non-trivial variants should not add a partial enum match clause, got {reqs:?}"
    );
    assert!(enss.is_empty(), "no ensures expected for by-value params");
}
