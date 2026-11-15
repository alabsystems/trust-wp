//@ expect: reject
//@ mechanism: a `match` arm whose value does not fit in `i64` (`1u128 << 100`, `i128::MIN`) wrote
//@ mechanism: the memory the `proof_assert!` reads, and the substitution walk's switch merge skipped
//@ mechanism: the arm (`switch_value_to_i64` returned None), folding the paths into the otherwise
//@ mechanism: branch's value: `*x = 0; match v { 1 << 100 => *x = 5, _ => {} }` read `*x == 0` on
//@ mechanism: every path (b1, and b8 for `i128::MIN`), and so did a plain local (widel).
//@ accept-means: a value a wide match arm writes is read as the value the other arms leave.
//@ WHY THE CONTRACT IS FALSE: `b1(&mut 9, 1 << 100)` leaves `*x == 5`; `b8(&mut 9, i128::MIN)` too;
//@ WHY THE CONTRACT IS FALSE: `widel(1 << 100)` leaves `y == 5`.
//@ fixed-by: D-186 (the merge guards every arm with its value-exact `discr == K`; an arm with no
//@ fixed-by: exact term is merged under an unconstrained guard, never dropped)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on 4c67cea8 (D-185) the three proof_asserts were VERIFIED and the crate ACCEPTED; with
//@ teeth: D-186 widel is FAILED (the merge keeps the arm) and b1, b8 are refused as stale reads.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn b1(x: &mut i32, v: u128) {
    *x = 0i32;
    match v {
        0x10000000000000000000000000u128 => {
            *x = 5i32;
        }
        _ => {}
    }
    proof_assert!(*x == 0i32);
}

pub fn b8(x: &mut i32, v: i128) {
    *x = 0i32;
    match v {
        -170141183460469231731687303715884105728i128 => {
            *x = 5i32;
        }
        _ => {}
    }
    proof_assert!(*x == 0i32);
}

pub fn widel(v: u128) {
    let mut y = 0i32;
    match v {
        0x10000000000000000000000000u128 => {
            y = 5i32;
        }
        _ => {}
    }
    proof_assert!(y == 0i32);
}
