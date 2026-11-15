//@ expect: reject
//@ mechanism: D-38's stale-entry-fact guard names a loop-written argument local by its MIR index, and read `_k` as the (k-1)th SOURCE parameter. A closure body's MIR puts its environment in `_1` and its first declared parameter in `_2`, so for a closure the guard named the NEXT parameter: here it dropped the entry fact about `y`, which no loop writes, and kept `(*z)@ == 7`, which the loop has falsified. The fact then discharged the assertion after the loop.
//@ accept-means: an assertion about a closure's by-reference parameter after a loop that overwrote its pointee is discharged by the closure's entry precondition, and the closure is credited.
//@ WHY THE ASSERTION IS FALSE: the loop body runs once and sets `*z` to 3.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: the assertion `verified ✓` on two contract preconditions and `parent::{closure#0} verified ✓`. The requires are two clauses on purpose: as one conjunction the wrongly named `y` dropped the `z` fact with it, and the case had no teeth.
//@ fixed-by: D-106 — `name_invalidated_args` offsets a closure's locals by its environment
//@ fn-failed: parent::{closure#0}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn parent() {
    let c = #[requires((*z)@ == 7)]
    #[requires((*y)@ == 7)]
    #[ensures(true)]
    |z: &mut u32, y: &mut u32| {
        let mut i = 0u32;
        #[invariant(i@ <= 1)]
        while i < 1 {
            *z = 3;
            i += 1;
        }
        proof_assert!((*z)@ == 7);
        let _ = y;
    };
    let _ = c;
}
