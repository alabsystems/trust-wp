//@ expect: reject
//@ verdict: unknown
//@ refused-with: loop call obligations: refutation withheld: goal set carries a fail-closed `false`
//@ mechanism: the loop condition `{ zero(r); r = &mut u; n < 3 }` hands `zero` the pointer `r`
//@ mechanism: before re-targeting it at `u`, a local nothing after the loop reads. The pass that
//@ mechanism: leaves the loop hands it the `&mut x` the last body pass stored, so `zero` writes `x`,
//@ mechanism: which the function returns; the exit and continuation read the header state, where
//@ mechanism: the invariant `x == 7u32` holds. A path borrow of an unread local exempts its pointer
//@ mechanism: only when it is the pointer's one change in the body.
//@ accept-means: the loop lane proved a postcondition over the header state for a local a callee
//@ accept-means: wrote through a pointer on the pass that left the loop. Concretely: `go()` returns
//@ accept-means: 0: the last body pass points `r` at `x`, and the exit pass's `zero(r)` stores 0.
//@ also-verified: zero
//@ fixed-by: D-229 (`loop_condition_exit_write`, the one-change rule for a path borrow).
//@ teeth: FAILED (loop invariant) at the campaign tip. On this branch without the one-change rule
//@ teeth: `go` is `unknown` only because the loop VC does not state `zero`'s postcondition, a
//@ teeth: withholding the D-229 marker does not need; `refused-with:` fails there and holds with
//@ teeth: it (the `loop-condition-exit-write` marker).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(^k == 0u32)]
pub fn zero(k: &mut u32) {
    *k = 0;
}

#[ensures(result == 7u32)]
pub fn go() -> u32 {
    let mut x = 7u32;
    let mut t = 0u32;
    let mut u = 0u32;
    let mut n = 0u32;
    let mut r: &mut u32 = &mut t;
    #[invariant(n <= 3u32)]
    #[invariant(x == 7u32)]
    while { zero(r); r = &mut u; n < 3 } {
        n += 1;
        if n == 3 {
            r = &mut x;
        }
    }
    x
}
