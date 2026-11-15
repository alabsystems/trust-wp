//@ expect: verify
//@ xfail: `dropper_loop` is `unknown (refutation withheld: goal set carries a fail-closed `false`
//@ xfail: ...)`, never FAILED: the walker's `Drop` arm owes a fail-closed `false` for any
//@ xfail: unchecked user `Drop::drop`, whether or not it panics. Retire this directive when a
//@ xfail: user `Drop::drop` body is verified and its contract charged at the drop.
//@ xfail-verdict: unknown
//@ mechanism: the value twin of s62m_drop_glue_unannotated_loop: the identical loop, whose
//@ mechanism: `Drop::drop` does NOT panic, so `dropper_loop` returns `x` and its contract is
//@ mechanism: TRUE. The loop path guards the marker (`i < 1 ==> false`); any model of the guard
//@ mechanism: refutes it, which shows only that the drop is reached (D-141, a guarded marker is a
//@ mechanism: marker). `xfail-verdict: unknown` keeps that model from being printed as a
//@ mechanism: counterexample to this program.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

struct D;

impl Drop for D {
    fn drop(&mut self) {}
}

#[ensures(result@ == x@)]
pub fn dropper_loop(x: u8) -> u8 {
    let mut i = 0u8;
    while i < 1u8 {
        let _d = D;
        i += 1u8;
    }
    x
}
