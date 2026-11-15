//@ expect: reject
//@ mechanism: a `proof_assert!` in a loop body reads a pointee a store later in the body writes: the
//@ mechanism: back edge carries that store into the next iteration's assertion. `*x = 0; while i <
//@ mechanism: n { proof_assert!(*x == 0); *x = 5; .. }` (l3), `for` with `*x += 1` (l3d), a store
//@ mechanism: under a condition (l3e), and a store before the assertion whose value is computed from
//@ mechanism: the counter (luniq). The substitution walk follows each acyclic path once, so it reads
//@ mechanism: the first iteration's value, and D-185 took that as the current one because every write
//@ mechanism: reaching the assertion was a whole-pointee store through `x`.
//@ accept-means: an assertion in a loop is credited from the value the memory has on the first
//@ accept-means: iteration only.
//@ WHY THE CONTRACT IS FALSE: with n = 2 the second iteration asserts `*x == 0` where l3/l3d/l3e left
//@ WHY THE CONTRACT IS FALSE: 5, 1 and 5, and luniq's `*x` is 1.
//@ fixed-by: D-186 (a store on a cycle of the CFG is never the recorded value of a read, and a
//@ fixed-by: store and the pre-loop value joining at the loop head are two definitions)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on 4c67cea8 (D-185) every proof_assert here was VERIFIED, and l3, l3e and luniq with
//@ teeth: their functions (l3d's function FAILED on its overflow check on both trees); with D-186
//@ teeth: each assertion is refused as a stale read.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn l3(x: &mut i32, n: u32) {
    *x = 0i32;
    let mut i = 0u32;
    while i < n {
        proof_assert!(*x == 0i32);
        *x = 5i32;
        i += 1;
    }
}

pub fn l3d(x: &mut i32, n: u32) {
    *x = 0i32;
    for _i in 0..n {
        proof_assert!(*x == 0i32);
        *x = *x + 1i32;
    }
}

pub fn l3e(x: &mut i32, n: u32) {
    *x = 0i32;
    let mut i = 0u32;
    while i < n {
        proof_assert!(*x == 0i32);
        if i == 0u32 {
            *x = 5i32;
        }
        i += 1;
    }
}

pub fn luniq(x: &mut i32, n: u32) {
    let mut i = 0u32;
    while i < n {
        *x = i as i32;
        proof_assert!(*x == 0i32);
        i += 1;
    }
}
