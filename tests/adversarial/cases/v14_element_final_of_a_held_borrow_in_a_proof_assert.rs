//@ expect: reject
//@ mechanism: `^` of a borrow an ELEMENT holds, reached through a `&mut` parameter (`^x[0]`, `^x[1]`,
//@ mechanism: `^x[0][0]`), or of a field or tuple element under an element (`^x[0].m` with `m`
//@ mechanism: declared `&mut i32`, `^x[0].0`), in a `proof_assert!`. Phase 1f looked only at a field
//@ mechanism: getter directly under `^`, and `projection_place_sort` gave an `index_logic` holder no
//@ mechanism: sort and no reference, so nothing was refused and Phase 3 read `^x[0]` as `(^x)[0]`:
//@ mechanism: the element the OUTER borrow is left with, which an untouched body leaves equal to
//@ mechanism: `(*x)[0]`. An array parameter carries no sort annotation, so the encoder cannot type
//@ mechanism: the element; the assertion's own text is read instead (D-129).
//@ accept-means: an assertion that a borrow the caller keeps (an element, or a field of one) is
//@ accept-means: resolved at the assertion is credited.
//@ WHY THE CONTRACT IS FALSE: each element borrow is the caller's after the call: `caller` writes 7
//@ WHY THE CONTRACT IS FALSE: through `arr[0]` after `idx` returns, so `^x[0]` is 7 while `*x[0]` was 1
//@ WHY THE CONTRACT IS FALSE: at the assertion (and `a` is 7, so `caller`'s `result == 1` is false).
//@ fixed-by: D-129 (an assertion's final read of a value no name denotes as a borrow is refused)
//@ refused-with: proof_assert in creusot_test::idx error: final value refused
//@ teeth: MEASURED (debug driver, ay 57a37e51): on 2c859203 the assertions of idx, idx_bool,
//@ teeth: idx_second, idx_nested, idx_struct_field and idx_tuple_elem were VERIFIED and idx_vec's was
//@ teeth: unknown with ay_result=unsat (the strict proof-authority gate alone); with D-129 all seven are
//@ teeth: refused before encoding, and `caller` stays unknown (fail-closed) on both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

pub fn idx(x: &mut [&mut i32; 1]) {
    proof_assert!(^x[0] == *x[0]);
}

pub fn idx_bool(x: &mut [&mut bool; 1]) {
    proof_assert!(^x[0] == *x[0]);
}

pub fn idx_second(x: &mut [&mut i32; 2]) {
    proof_assert!(^x[1] == *x[1]);
}

pub fn idx_nested(x: &mut [[&mut i32; 1]; 1]) {
    proof_assert!(^x[0][0] == *x[0][0]);
}

pub fn idx_struct_field(x: &mut [M<'_>; 1]) {
    proof_assert!(^x[0].m == *x[0].m);
}

pub fn idx_tuple_elem(x: &mut [(&mut i32, i32); 1]) {
    proof_assert!(^x[0].0 == *x[0].0);
}

pub fn idx_vec(x: &mut Vec<&mut i32>) {
    proof_assert!(x@.len() >= 1 ==> ^x[0] == *x[0]);
}

#[ensures(result == 1i32)]
pub fn caller() -> i32 {
    let mut a = 1i32;
    {
        let mut arr = [&mut a];
        idx(&mut arr);
        *arr[0] = 7i32;
    }
    a
}
