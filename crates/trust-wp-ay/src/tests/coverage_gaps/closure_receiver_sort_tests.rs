// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `find_postcondition_mut_receiver_sort` (#1998 coverage gap).
//!
//! This `pub(crate)` method walks a `PureExpr` tree to find `postcondition_mut`
//! calls where a given variable appears as the state argument or receiver, and
//! returns the receiver's ay sort. It is called from `infer_existential_var_sort`
//! (priority 2-3 fallback) and `pure_quantifier.rs`.
//!
//! Without direct tests, a regression in tree walking (e.g., missing a variant)
//! would silently cause Sort::Int fallback for existential Skolem variables.

use std::sync::Arc;

use ntest::timeout;
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::*;

/// Extract the sort name string for comparison. `register_structured_sort`
/// returns `Datatype(...)` but `solver.get_sort()` returns `Uninterpreted(name)`.
/// Both encode the same logical sort — compare by name.
fn sort_name(sort: &Sort) -> &str {
    match sort {
        Sort::Uninterpreted(name) => name.as_str(),
        Sort::Datatype(dt) => dt.name.as_str(),
        Sort::Int => "Int",
        Sort::Bool => "Bool",
        _ => "other",
    }
}

fn register_closure_sort(encoder: &mut AYEncoder, def_id: &str) -> Sort {
    encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: def_id.to_string(),
                captures: vec![],
            },
        )
        .expect("closure sort registration should succeed")
}

fn seed_postcondition_mut_decl(
    encoder: &mut AYEncoder,
    receiver: &str,
    receiver_sort: Sort,
    state: &str,
    state_sort: Sort,
) {
    encoder
        .get_or_declare_var(receiver, receiver_sort)
        .expect("receiver declaration should succeed");
    encoder
        .get_or_declare_var(state, state_sort)
        .expect("state declaration should succeed");
    encoder
        .encode_pure(&method_call(
            var(receiver),
            "postcondition_mut",
            vec![var("x"), var(state), var("r")],
        ))
        .expect("postcondition_mut declaration should succeed");
}

fn has_postcondition_mut_domain(
    encoder: &AYEncoder,
    expected_receiver_sort: &Sort,
    expected_state_sort: &Sort,
) -> bool {
    encoder.decls().logic_funcs_iter().any(|(name, decl)| {
        name.starts_with("closure_postcondition_mut_")
            && decl.domain().len() == 4
            && sort_name(&decl.domain()[0]) == sort_name(expected_receiver_sort)
            && sort_name(&decl.domain()[2]) == sort_name(expected_state_sort)
    })
}

/// When the target variable appears as the state argument (second-to-last position)
/// in a `postcondition_mut` call and the receiver has a registered non-Int sort,
/// the method should return that receiver sort.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_var_is_state_arg_returns_receiver_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Register `f` with a ClosureEnv sort (non-Int) so resolve_receiver_sort
    // can find it.
    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: "crate::test::closure_recv#0".to_string(),
                captures: vec![],
            },
        )
        .unwrap();
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    // Build: f.postcondition_mut(x, st1, r)
    // st1 is at args[1] which is args[len-2] when len==3
    let body = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("st1"), var("r")],
    );

    let result = encoder.find_postcondition_mut_receiver_sort("st1", &body);
    assert!(
        result.is_some(),
        "should find receiver sort when var is state arg"
    );
    let found = result.unwrap();
    assert_ne!(found, Sort::Int, "should not fall back to Int");
    assert_eq!(
        sort_name(&found),
        sort_name(&closure_sort),
        "should return the receiver's closure env sort name"
    );
}

/// When the target variable appears as the receiver of `postcondition_mut`,
/// the method should return the receiver's sort.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_var_is_receiver_returns_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: "crate::test::closure_recv_as_receiver#0".to_string(),
                captures: vec![],
            },
        )
        .unwrap();
    encoder
        .get_or_declare_var("st1", closure_sort.clone())
        .expect("declare st1 with closure sort");

    // Build: st1.postcondition_mut((), st2, result)
    // st1 IS the receiver
    let body = method_call(
        var("st1"),
        "postcondition_mut",
        vec![var("unit"), var("st2"), var("result")],
    );

    let result = encoder.find_postcondition_mut_receiver_sort("st1", &body);
    assert!(
        result.is_some(),
        "should find receiver sort when var is receiver"
    );
    let found = result.unwrap();
    assert_ne!(found, Sort::Int, "should not fall back to Int");
    assert_eq!(
        sort_name(&found),
        sort_name(&closure_sort),
        "should return the receiver's closure env sort name"
    );
}

/// When the target variable does not appear in any `postcondition_mut` call,
/// the method should return None.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_var_absent_returns_none() {
    let encoder = AYEncoder::new_with_quantifiers();

    // Build: f.postcondition_mut(x, st1, r) — but search for "absent_var"
    let body = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("st1"), var("r")],
    );

    let result = encoder.find_postcondition_mut_receiver_sort("absent_var", &body);
    assert!(
        result.is_none(),
        "should return None when var is not in postcondition_mut"
    );
}

/// When `postcondition_mut` is nested inside a `Let` binding, the tree walker
/// should still find it. This exercises the Let recursion arm.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_nested_in_let_binding() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: "crate::test::closure_let_nested#0".to_string(),
                captures: vec![],
            },
        )
        .unwrap();
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    // Build: let mid = helper(x) in f.postcondition_mut(a, st1, mid)
    let inner_mut = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("st1"), var("mid")],
    );
    let body = let_bind("mid", logic_fn_call("helper", vec![var("x")]), inner_mut);

    let result = encoder.find_postcondition_mut_receiver_sort("st1", &body);
    assert!(
        result.is_some(),
        "should find receiver sort through Let wrapper"
    );
    let found = result.unwrap();
    assert_ne!(found, Sort::Int, "should not fall back to Int");
    assert_eq!(sort_name(&found), sort_name(&closure_sort));
}

/// When `postcondition_mut` is nested inside a `BinOp` (e.g., conjunction),
/// the tree walker should still find it.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_nested_in_binop() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: "crate::test::closure_binop_nested#0".to_string(),
                captures: vec![],
            },
        )
        .unwrap();
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    // Build: true && f.postcondition_mut(a, st1, r)
    let inner_mut = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("a"), var("st1"), var("r")],
    );
    let body = PureExpr::BinOp(
        Arc::new(PureExpr::Bool(true)),
        BinOp::And,
        Arc::new(inner_mut),
    );

    let result = encoder.find_postcondition_mut_receiver_sort("st1", &body);
    assert!(
        result.is_some(),
        "should find receiver sort through BinOp wrapper"
    );
    let found = result.unwrap();
    assert_ne!(found, Sort::Int, "should not fall back to Int");
    assert_eq!(sort_name(&found), sort_name(&closure_sort));
}

/// A non-`postcondition_mut` method call should not match, even when the
/// variable appears in the args at the state-arg position.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_non_postcondition_mut_method_returns_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    let closure_sort = encoder
        .register_structured_sort(
            crate::encoder::sort_context::StructuredSortContext::ClosureStruct {
                def_id: "crate::test::closure_wrong_method#0".to_string(),
                captures: vec![],
            },
        )
        .unwrap();
    encoder
        .get_or_declare_var("f", closure_sort)
        .expect("declare f with closure sort");

    // Build: f.postcondition_once(x, st1, r) — NOT postcondition_mut
    let body = method_call(
        var("f"),
        "postcondition_once",
        vec![var("x"), var("st1"), var("r")],
    );

    let result = encoder.find_postcondition_mut_receiver_sort("st1", &body);
    assert!(
        result.is_none(),
        "postcondition_once should not match postcondition_mut tree walker"
    );
}

/// `encode_with_recursive_existential_skolemization` should preserve an
/// explicit Bool annotation instead of inheriting the closure receiver sort.
#[test]
#[timeout(30000)]
fn test_skolemization_prefers_explicit_annotation_over_receiver_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::annotated_state#0");
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    let existential = exists_with_sort(
        "state",
        ExprSort::Bool,
        method_call(
            var("f"),
            "postcondition_mut",
            vec![var("x"), var("state"), var("r")],
        ),
    );

    encoder
        .encode_with_recursive_existential_skolemization(&existential)
        .expect("skolemization should succeed");

    assert!(
        has_postcondition_mut_domain(&encoder, &closure_sort, &Sort::Bool),
        "explicit Bool annotation should determine the Skolem/state domain sort"
    );
}

/// Unannotated existential state variables should inherit the closure receiver
/// sort when the receiver already has a non-Int runtime sort.
#[test]
#[timeout(30000)]
fn test_skolemization_inherits_runtime_receiver_sort_for_state_arg() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::state_arg#0");
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    let existential = exists(
        "state",
        method_call(
            var("f"),
            "postcondition_mut",
            vec![var("x"), var("state"), var("r")],
        ),
    );

    encoder
        .encode_with_recursive_existential_skolemization(&existential)
        .expect("skolemization should succeed");

    assert!(
        has_postcondition_mut_domain(&encoder, &closure_sort, &closure_sort),
        "receiver sort should propagate into the Skolem/state domain sort"
    );
}

/// Deref-wrapped receivers should recurse through `resolve_receiver_sort`
/// instead of falling back to Int during Skolemization.
#[test]
#[timeout(30000)]
fn test_skolemization_inherits_deref_receiver_sort_for_state_arg() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::state_arg_deref#0");
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    let existential = exists(
        "state",
        method_call(
            deref(var("f")),
            "postcondition_mut",
            vec![var("x"), var("state"), var("r")],
        ),
    );

    encoder
        .encode_with_recursive_existential_skolemization(&existential)
        .expect("skolemization should succeed");

    assert!(
        has_postcondition_mut_domain(&encoder, &closure_sort, &closure_sort),
        "deref receivers should still propagate the closure env sort"
    );
}

/// When the receiver still has runtime `Sort::Int`, the skolemization path
/// should recover the closure env sort from already-declared
/// `closure_postcondition_mut_*` UFs instead of introducing an Int-sorted state.
#[test]
#[timeout(30000)]
fn test_skolemization_recovers_declared_closure_sort_from_int_receiver() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::state_arg_fallback#0");

    seed_postcondition_mut_decl(
        &mut encoder,
        "template_f",
        closure_sort.clone(),
        "template_state",
        closure_sort.clone(),
    );
    encoder
        .get_or_declare_var("f", Sort::Int)
        .expect("declare f with generic Int sort");

    let existential = exists(
        "state",
        method_call(
            var("f"),
            "postcondition_mut",
            vec![var("x"), var("state"), var("r")],
        ),
    );

    encoder
        .encode_with_recursive_existential_skolemization(&existential)
        .expect("skolemization should succeed");

    assert!(
        has_postcondition_mut_domain(&encoder, &Sort::Int, &closure_sort),
        "declared closure_postcondition_mut UFs should prevent Int fallback on the state sort"
    );
}

// ── resolve_receiver_sort direct coverage (#1998 P1-1087) ────────────

/// When the receiver variable has a non-Int sort (e.g., ClosureEnv),
/// `resolve_receiver_sort` should return that sort directly without
/// falling through to the UF-based lookup.
#[test]
#[timeout(30000)]
fn test_resolve_receiver_sort_non_int_var_returns_directly() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::resolve_direct#0");
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    let receiver = var("f");
    let result = encoder.find_postcondition_mut_receiver_sort(
        "unused_state",
        &method_call(
            receiver,
            "postcondition_mut",
            vec![var("x"), var("unused_state"), var("r")],
        ),
    );
    // The receiver "f" has closure_sort, so resolve_receiver_sort should find it
    // (though find_postcondition_mut_receiver_sort looks at whether var matches state arg)
    assert!(result.is_some(), "should find receiver sort for state arg");
    assert_eq!(
        sort_name(&result.unwrap()),
        sort_name(&closure_sort),
        "should return the closure env sort from the non-Int receiver"
    );
}

/// When the receiver variable has Sort::Int AND no declared postcondition_mut
/// UFs exist, `resolve_receiver_sort` should return None (not Some(Int)).
#[test]
#[timeout(30000)]
fn test_resolve_receiver_sort_int_var_no_ufs_returns_none() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    encoder
        .get_or_declare_var("f", Sort::Int)
        .expect("declare f with Int sort");

    // No postcondition_mut UFs seeded — resolve should fall through to
    // infer_closure_env_sort_from_declared_ufs which returns None
    let receiver = var("f");
    let result = encoder.find_postcondition_mut_receiver_sort(
        "st",
        &method_call(
            receiver,
            "postcondition_mut",
            vec![var("x"), var("st"), var("r")],
        ),
    );
    assert!(
        result.is_none(),
        "Int receiver with no declared UFs should return None, not Some(Int)"
    );
}

/// When the receiver variable has Sort::Int but postcondition_mut UFs ARE
/// declared, `resolve_receiver_sort` should recover the closure env sort
/// from the UF domain (via `infer_closure_env_sort_from_declared_ufs`).
#[test]
#[timeout(30000)]
fn test_resolve_receiver_sort_int_var_with_ufs_recovers_closure_sort() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::resolve_ufs#0");

    // Seed a postcondition_mut UF so the fallback can find the closure env sort
    seed_postcondition_mut_decl(
        &mut encoder,
        "template_f",
        closure_sort.clone(),
        "template_state",
        closure_sort.clone(),
    );
    encoder
        .get_or_declare_var("f", Sort::Int)
        .expect("declare f with Int sort");

    let receiver = var("f");
    let result = encoder.find_postcondition_mut_receiver_sort(
        "st",
        &method_call(
            receiver,
            "postcondition_mut",
            vec![var("x"), var("st"), var("r")],
        ),
    );
    assert!(
        result.is_some(),
        "Int receiver with declared UFs should recover closure sort"
    );
    assert_eq!(
        sort_name(&result.unwrap()),
        sort_name(&closure_sort),
        "should recover the closure env sort from declared UFs"
    );
}

// ── infer_existential_var_sort direct fallback (#1998 P1-1087) ────────

/// When an existential body contains NO `postcondition_mut` call, the
/// Skolemization path is skipped entirely and standard quantifier encoding
/// is used. This boundary test verifies the standard path handles
/// non-postcondition_mut existentials without error.
#[test]
#[timeout(30000)]
fn test_existential_without_postcondition_mut_uses_standard_encoding() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Existential with NO postcondition_mut in body, NO annotation.
    // The body is just a BinOp — no method call at all.
    let existential = exists(
        "witness",
        PureExpr::BinOp(
            Arc::new(var("witness")),
            BinOp::Eq,
            Arc::new(PureExpr::Int(42)),
        ),
    );

    // Skolemization checks body_has_postcondition_mut_with_var (false) and
    // body_has_any_postcondition_mut (false), then falls through to
    // standard encode_pure encoding.
    let result = encoder.encode_with_recursive_existential_skolemization(&existential);
    assert!(
        result.is_ok(),
        "non-postcondition_mut existential should use standard encoding path"
    );
}

/// When the existential var appears in postcondition_mut but the receiver
/// is an undeclared variable (not in self.vars), both resolve_receiver_sort
/// and infer_closure_env_sort_from_declared_ufs fail, triggering the
/// Sort::Int fallback at fn_mut_once.rs:366.
#[test]
#[timeout(30000)]
fn test_infer_existential_var_sort_unknown_receiver_falls_to_int() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Don't declare "unknown_f" in encoder — receiver lookup will fail
    let existential = exists(
        "state",
        method_call(
            var("unknown_f"),
            "postcondition_mut",
            vec![var("x"), var("state"), var("r")],
        ),
    );

    // Skolemization will fire (body has postcondition_mut with var "state")
    // but receiver sort inference will fall back to Int since "unknown_f"
    // is neither declared nor are there existing postcondition_mut UFs.
    let result = encoder.encode_with_recursive_existential_skolemization(&existential);
    assert!(
        result.is_ok(),
        "skolemization with unknown receiver should succeed (Int fallback)"
    );
}

// ── Depth stress: find_postcondition_mut_receiver_sort (#1998 P1-1087) ──

/// Build a deeply nested BinOp chain wrapping a postcondition_mut call.
/// At depth=100, the recursive walker stays below `MAX_ENCODING_DEPTH`
/// and should still find the nested call.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_depth_100_survives() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::depth_stress#0");
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    // Build: true && (true && (true && ... (f.postcondition_mut(x, st, r))))
    // with 100 levels of BinOp nesting
    let mut expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("st"), var("r")],
    );
    for _ in 0..100 {
        expr = PureExpr::BinOp(Arc::new(PureExpr::Bool(true)), BinOp::And, Arc::new(expr));
    }

    let result = encoder.find_postcondition_mut_receiver_sort("st", &expr);
    assert!(
        result.is_some(),
        "depth-100 nesting should still find the postcondition_mut call"
    );
    assert_eq!(sort_name(&result.unwrap()), sort_name(&closure_sort));
}

/// Build a deep Ite chain wrapping postcondition_mut.
/// Exercises the Ite arm of the recursive walker at significant depth.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_deep_ite_chain_survives() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::ite_depth#0");
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    // Build: if true then (if true then ... (f.postcondition_mut(x, st, r))) else false
    let mut expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("st"), var("r")],
    );
    for _ in 0..80 {
        expr = PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(expr),
            Arc::new(PureExpr::Bool(false)),
        );
    }

    let result = encoder.find_postcondition_mut_receiver_sort("st", &expr);
    assert!(
        result.is_some(),
        "depth-80 Ite nesting should still find the postcondition_mut call"
    );
    assert_eq!(sort_name(&result.unwrap()), sort_name(&closure_sort));
}

/// Deep nesting through mixed expression types: BinOp → MethodCall → Let → Ite.
/// Exercises multiple arms of the recursive walker in a single traversal.
#[test]
#[timeout(30000)]
fn test_find_receiver_sort_mixed_deep_nesting_survives() {
    let mut encoder = AYEncoder::new_with_quantifiers();
    let closure_sort = register_closure_sort(&mut encoder, "crate::test::mixed_depth#0");
    encoder
        .get_or_declare_var("f", closure_sort.clone())
        .expect("declare f with closure sort");

    let mut expr = method_call(
        var("f"),
        "postcondition_mut",
        vec![var("x"), var("st"), var("r")],
    );
    // Alternate: BinOp -> method_call wrapper -> Let -> Ite, ~25 rounds = 100 levels
    for i in 0..25 {
        let wrapper_name = format!("wrap_{i}");
        expr = PureExpr::BinOp(Arc::new(PureExpr::Bool(true)), BinOp::And, Arc::new(expr));
        expr = method_call(var("g"), &wrapper_name, vec![expr]);
        expr = let_bind(&format!("tmp_{i}"), PureExpr::Int(0), expr);
        expr = PureExpr::Ite(
            Arc::new(PureExpr::Bool(true)),
            Arc::new(expr),
            Arc::new(PureExpr::Bool(false)),
        );
    }

    let result = encoder.find_postcondition_mut_receiver_sort("st", &expr);
    assert!(
        result.is_some(),
        "100-level mixed nesting should survive without stack overflow"
    );
    assert_eq!(sort_name(&result.unwrap()), sort_name(&closure_sort));
}
