//@ expect: reject
//@ mechanism: `^` of a field of the parameter's FINAL value (`^(^x).m`, `^(^x).s.m`), field declared
//@ mechanism: `&mut i32`: `(^x).m` is the borrow the referent is left holding, which an untouched
//@ mechanism: body leaves as the caller's own borrow, so its final value is the caller's to decide.
//@ mechanism: The contract lane's `held_through_a_mutable_parameter` walked `*` and field getters
//@ mechanism: down to the parameter's NAME (`holds` exempts `^x`), and Phase 1f read `^x` as a place
//@ mechanism: not reached through a reference; Phase 3 then read it as the field of the holder's
//@ mechanism: final value, and the crate was ACCEPTED (D-129).
//@ accept-means: a contract stating that the borrow the caller keeps inside `*x` ends at its current
//@ accept-means: value is credited.
//@ WHY THE CONTRACT IS FALSE: `let mut m = M { m: &mut a }; final_field(&mut m); *m.m = 7;` ends the
//@ WHY THE CONTRACT IS FALSE: inner borrow at 7 while `*(^x).m` is the entry value 1.
//@ fixed-by: D-129 (the contract lane walks `^`, branches, elements and views to the parameter; an
//@ fixed-by: assertion's final read of a value no name denotes as a borrow is refused)
//@ refused-with: final value of a value held through the `&mut` parameter `x`
//@ teeth: MEASURED (debug driver, ay 57a37e51): on 2c859203 final_field, final_nested,
//@ teeth: final_field_cur and final_ite were VERIFIED and pa_final_field's assertion was VERIFIED, and the
//@ teeth: crate was ACCEPTED; with D-129 the four contracts are refused at placement and the assertion
//@ teeth: before encoding.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

pub struct N<'a> {
    pub s: M<'a>,
}

#[ensures(^(^x).m == *(^x).m)]
pub fn final_field(x: &mut M<'_>) {}

#[ensures(^(^x).s.m == *(^x).s.m)]
pub fn final_nested(x: &mut N<'_>) {}

#[ensures(^(^x).m == *(*x).m)]
pub fn final_field_cur(x: &mut M<'_>) {}

#[ensures(^(if c { ^x } else { ^x }).m == *(^x).m)]
pub fn final_ite(x: &mut M<'_>, c: bool) {}

pub fn pa_final_field(x: &mut M<'_>) {
    proof_assert!(^(^x).m == *(^x).m);
}
