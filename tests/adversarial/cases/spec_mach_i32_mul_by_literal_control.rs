//@ expect: verify
//@ mechanism: control: a machine-integer product in a postcondition, `^x == *x * 2i32`. D-232
//@ mechanism: states the oracle's wrapping product as a Euclidean `mod`.
//@ WHY THE CONTRACT IS TRUE: *x lies in [i32::MIN / 2, i32::MAX / 2], so *x * 2 does not wrap.
//@ xfail: ay computes the UNSAT and withholds it (`proof-trusted`): the product's `mod` does not
//@ xfail: certify.
//@ xfail-verdict: unknown
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*x >= -1073741824i32 && *x <= 1073741823i32)]
#[ensures(^x == *x * 2i32)]
pub fn double_mut(x: &mut i32) {
    *x *= 2;
}
