//@ expect: verify
//@ xfail: `evil` is `unknown (refutation withheld: goal set carries a fail-closed `false` ...)`,
//@ xfail: never FAILED: `make::<D>` drops a `D` whose user `Drop::drop` is unchecked, and the
//@ xfail: call owes a fail-closed `false` for it whether or not it panics. Retire this directive
//@ xfail: when a user `Drop::drop` body is verified and its contract charged at the drop.
//@ xfail-verdict: unknown
//@ mechanism: the value twin of s62v2_preloop_fnptr_credit_no_owe: the identical pre-loop fn
//@ mechanism: pointer and loop, whose `Drop::drop` does NOT panic, so `make` returns 7, `need7`'s
//@ mechanism: precondition holds and `evil`'s contract is TRUE. The drop-glue marker sits behind
//@ mechanism: the loop's path guard; a model of the guard refutes it, which shows only that the
//@ mechanism: drop is reached (D-141, a guarded marker is a marker).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct D;

impl Drop for D {
    fn drop(&mut self) {}
}

#[ensures(result == 7u32)]
pub fn make<T>(_t: T) -> u32 {
    7u32
}

#[requires(y == 7u32)]
#[ensures(true)]
pub fn need7(y: u32) {}

#[ensures(true)]
pub fn evil(n: u32) {
    let f: fn(D) -> u32 = make::<D>;
    let mut i = 0u32;
    while i < n {
        let r = f(D);
        need7(r);
        i = i.wrapping_add(1u32);
    }
}
