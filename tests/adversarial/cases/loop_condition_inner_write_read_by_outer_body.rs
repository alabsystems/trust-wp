//@ expect: reject
//@ mechanism: an inner loop's block condition `{ let b = m < 3; i = 0; b }` writes `i` on the pass
//@ mechanism: that leaves the inner loop, and the outer loop's body reads `i` right after it
//@ mechanism: (`r = i`). The inner exit and the outer body's continuation read the inner header
//@ mechanism: state, where the inner invariant `i == 7u32` holds, so the outer invariant
//@ mechanism: `r == 7u32` is preserved over a value the program does not hold. The code after the
//@ mechanism: inner loop is the rest of the outer body, not the rest of the function.
//@ accept-means: the loop lane proved an outer invariant and a postcondition over the inner header
//@ accept-means: state for a value the inner exit path overwrote. Concretely: `go()` returns 0: the
//@ accept-means: inner loop's fourth condition evaluation stores `i = 0`, and `r = i` copies it.
//@ fixed-by: D-220 (the outer body walk havocs what an inner loop may write) refutes the outer
//@ fixed-by: invariant's preservation; D-229 (`loop_condition_exit_write`) refuses the inner loop
//@ fixed-by: first, because the rest of the outer body reads what its exit path wrote.
//@ teeth: ACCEPTED at exit 0 at the campaign tip. On this branch without D-229 `go` is refuted
//@ teeth: `FAILED (loop invariant)`; with D-229 it is `unknown` (the `loop-condition-exit-write`
//@ teeth: marker).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 7u32)]
pub fn go() -> u32 {
    let mut n = 0u32;
    let mut r = 7u32;
    #[invariant(r == 7u32)]
    #[invariant(n <= 1u32)]
    while n < 1 {
        let mut i = 7u32;
        let mut m = 0u32;
        #[invariant(i == 7u32)]
        #[invariant(m <= 3u32)]
        while { let b = m < 3; i = 0; b } {
            i = 7;
            m += 1;
        }
        r = i;
        n += 1;
    }
    r
}
