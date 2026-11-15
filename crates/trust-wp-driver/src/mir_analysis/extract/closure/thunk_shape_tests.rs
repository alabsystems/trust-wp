// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Body-shape predicate of the exact-thunk rule: only a straight, call-free,
//! borrow-free path that assigns one literal to the return place is exact.

use trust_wp_core::formula::PureExpr;

use super::{exact_thunk_value_from_shape, ThunkStmtShape as S, ThunkTermShape as T};

fn lit(v: i64) -> S {
    S::ReturnConst(Some(PureExpr::Int(v)))
}

#[test]
fn literal_thunk_is_exact() {
    let blocks = vec![(vec![S::Inert, lit(3), S::Inert], T::Return)];
    assert_eq!(
        exact_thunk_value_from_shape(&blocks),
        Some(PureExpr::Int(3))
    );
}

#[test]
fn bool_literal_through_goto_chain_is_exact() {
    let blocks = vec![
        (vec![S::Inert], T::Goto(1)),
        (vec![S::ReturnConst(Some(PureExpr::Bool(true)))], T::Goto(2)),
        (vec![S::Inert], T::Return),
    ];
    assert_eq!(
        exact_thunk_value_from_shape(&blocks),
        Some(PureExpr::Bool(true))
    );
}

#[test]
fn loop_back_edge_rejects() {
    // `let mut x = 0; while x < 3 { x += 1 } x` after lowering keeps a cycle
    // (and a SwitchInt); even a pure Goto cycle must reject.
    let blocks = vec![(vec![lit(0)], T::Goto(1)), (vec![S::Inert], T::Goto(0))];
    assert_eq!(exact_thunk_value_from_shape(&blocks), None);
    let switch_loop = vec![(vec![lit(0)], T::Goto(1)), (vec![S::Other], T::Other)];
    assert_eq!(exact_thunk_value_from_shape(&switch_loop), None);
}

#[test]
fn mut_borrow_write_rejects() {
    // `let p = &mut x; *p = 2;` — a borrow and a write through a projection.
    let blocks = vec![(vec![S::Other, S::Other, lit(1)], T::Return)];
    assert_eq!(exact_thunk_value_from_shape(&blocks), None);
}

#[test]
fn panic_path_rejects() {
    // `if .. { panic!() } 1`: a SwitchInt/Call on the path, value in dead tail.
    let blocks = vec![(vec![], T::Other), (vec![lit(1)], T::Return)];
    assert_eq!(exact_thunk_value_from_shape(&blocks), None);
}

#[test]
fn call_terminator_rejects() {
    let blocks = vec![(vec![S::Inert], T::Other), (vec![lit(1)], T::Return)];
    assert_eq!(exact_thunk_value_from_shape(&blocks), None);
}

#[test]
fn match_switch_rejects() {
    let blocks = vec![
        (vec![S::Inert], T::Other),
        (vec![lit(1)], T::Return),
        (vec![lit(2)], T::Return),
    ];
    assert_eq!(exact_thunk_value_from_shape(&blocks), None);
}

#[test]
fn non_literal_or_untranslated_constant_rejects() {
    let untranslated = vec![(vec![S::ReturnConst(None)], T::Return)];
    assert_eq!(exact_thunk_value_from_shape(&untranslated), None);
    let var = vec![(
        vec![S::ReturnConst(Some(PureExpr::Var("x".into(), None)))],
        T::Return,
    )];
    assert_eq!(exact_thunk_value_from_shape(&var), None);
}

#[test]
fn zero_or_double_return_assignment_rejects() {
    let none = vec![(vec![S::Inert], T::Return)];
    assert_eq!(exact_thunk_value_from_shape(&none), None);
    let twice = vec![(vec![lit(1), lit(2)], T::Return)];
    assert_eq!(exact_thunk_value_from_shape(&twice), None);
}

#[test]
fn missing_block_rejects() {
    let blocks = vec![(vec![lit(1)], T::Goto(7))];
    assert_eq!(exact_thunk_value_from_shape(&blocks), None);
    assert_eq!(exact_thunk_value_from_shape(&[]), None);
}
