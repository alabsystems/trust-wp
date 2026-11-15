//@ expect: verify
//@ mechanism: control for the v20 cases (D-186): a `proof_assert!` reads a pointee whose ONE reaching
//@ mechanism: definition is a store the walk records: a join of another local's writes (t1), an
//@ mechanism: assertion inside the branch that stored (t2), a store after the join overwriting both
//@ mechanism: paths (t3), a store before a loop the loop never writes (t5), a store after a copy
//@ mechanism: taken through a shared reborrow (t6, and the copy's entry value, t7), a shared reference
//@ mechanism: parameter read beside a written one (t8), and wide `match` arms merged exactly (t4, t4n).
//@ accept-means: n/a (control)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified): every assertion and function
//@ teeth: verifies with D-186; on 4c67cea8 all did but t7 (unknown: the copy through the reborrow
//@ teeth: and the store shared `x_current`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn t1(x: &mut i32, c: bool) {
    let mut y = 0i32;
    *x = 0i32;
    if c {
        y = 1i32;
    }
    proof_assert!(*x == 0i32);
    proof_assert!(y == 0i32 || y == 1i32);
}

pub fn t2(x: &mut i32, c: bool) {
    *x = 0i32;
    if c {
        *x = 5i32;
        proof_assert!(*x == 5i32);
    }
}

pub fn t3(x: &mut i32, c: bool) {
    *x = 0i32;
    if c {
        *x = 5i32;
    }
    *x = 7i32;
    proof_assert!(*x == 7i32);
}

pub fn t4(v: u128) {
    let mut y = 0i32;
    match v {
        0x10000000000000000000000000u128 => {
            y = 5i32;
        }
        _ => {}
    }
    proof_assert!(y == 0i32 || y == 5i32);
}

pub fn t4n(v: i128) {
    let mut y = 0i32;
    match v {
        -170141183460469231731687303715884105728i128 => {
            y = 5i32;
        }
        _ => {}
    }
    proof_assert!(v == i128::MIN || y == 0i32);
}

pub fn t5(x: &mut i32, n: u32) {
    *x = 5i32;
    let mut i = 0u32;
    while i < n {
        proof_assert!(*x == 5i32);
        i += 1;
    }
}

#[requires(*x == 0i32)]
pub fn t6(x: &mut i32) {
    let r: &i32 = &*x;
    let _v = *r;
    *x = 5i32;
    proof_assert!(*x == 5i32);
}

#[requires(*x == 0i32)]
pub fn t7(x: &mut i32) {
    let r: &i32 = &*x;
    let v = *r;
    *x = 5i32;
    proof_assert!(v == 0i32);
}

pub fn t8(x: &i32, y: &mut i32) {
    let v = *x;
    *y = 5i32;
    proof_assert!(*x == v);
    proof_assert!(*y == 5i32);
}
