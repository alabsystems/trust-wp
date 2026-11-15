//@ expect: reject
//@ mechanism: a loop invariant reading the final value of a borrow an element or a field of a
//@ mechanism: `&mut` parameter holds (`^x[0]`, `^x.m`). The encoder reads such a `^` as the place
//@ mechanism: the outer borrow is left with, as it did in a `proof_assert!` (D-129); no guard
//@ mechanism: refused it in the loop lane.
//@ accept-means: a loop invariant about a held borrow's final value is credited, though the
//@ accept-means: caller decides it after the call.
//@ WHY THE CONTRACT IS FALSE: a caller writes 7 through `x[0]` (or `x.m`) after the call, so
//@ WHY THE CONTRACT IS FALSE: `^x[0] == *x[0]` is no fact of the function.
//@ fixed-by: D-129 (the loop lane refuses a final read of a value not named as a borrow)
//@ refused-with: loop invariant final value refused
//@ teeth: MEASURED (debug driver, ay 57a37e51): on 2c859203 both functions were FAILED (loop
//@ teeth: invariant, initialization check), not credited but refused by no guard; with the fix
//@ teeth: both are refused before encoding (`li_field`'s invariant reaches the lane as `^x.0`, a
//@ teeth: flattened field path).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct M<'a> {
    pub m: &'a mut i32,
}

pub fn li_idx(x: &mut [&mut i32; 1]) {
    let mut i = 0u32;
    #[invariant(^x[0] == *x[0])]
    while i < 1 {
        i += 1;
    }
}

pub fn li_field(x: &mut M<'_>) {
    let mut i = 0u32;
    #[invariant(^x.m == *x.m)]
    while i < 1 {
        i += 1;
    }
}
