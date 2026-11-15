//@ expect: reject
//@ mechanism: preservation twin of loop_body_call_postcondition_premise_control: `b` starts `true`,
//@ mechanism: so the invariant holds at entry, and the body's `go_m` returns false and says so. The
//@ mechanism: postcondition the body walk now states is what refutes preservation; a walk that
//@ mechanism: withheld the refutation, or proved it, would lose this.
//@ accept-means: `go_loop(1)` sets `b = false` on its first iteration, so `#[invariant(b)]` is
//@ accept-means: FALSE after it, and trust-wp proved the invariant preserved.
//@ verdict: failed
//@ fn-failed: go_loop
//@ also-verified: go_m
//@ teeth: not a false-accept gate: refuted `failed` before and after D-219. It pins the flavour,
//@ teeth: so a walk that withholds the refutation its own stated premise supports is flagged.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(!result)]
pub fn go_m() -> bool { false }

pub fn go_loop(n: u32) {
    let mut b = true;
    let mut i: u32 = 0;
    #[invariant(b)]
    while i < n {
        b = go_m();
        i += 1;
    }
}
