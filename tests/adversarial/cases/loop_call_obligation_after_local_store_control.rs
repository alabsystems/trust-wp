//@ expect: verify
//@ xfail: the argument `k` is read after a store through the borrow `r` of it, so the loop body
//@ xfail: walk replaces the call's precondition by the fail-closed marker under its path, and the
//@ xfail: refutation of the marker is withheld.
//@ xfail-verdict: unknown
//@ mechanism: control: the local-borrow spelling of loop_call_obligation_after_param_store_control.
//@ mechanism: `k` is 5 on every iteration, and the call was `FAILED (loop call obligations)` with a
//@ mechanism: validated model of the marker before D-225.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x == 5u32)]
pub fn need_five(x: u32) {}

pub fn f() {
    let mut k = 0u32;
    let r = &mut k;
    *r = 5;
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3 { need_five(k); i += 1; }
}
