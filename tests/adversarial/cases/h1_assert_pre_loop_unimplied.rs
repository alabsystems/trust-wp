//@ expect: reject
//@ mechanism: FRONT H step 1 — a plain `assert!` lowers to `SwitchInt(cond)` whose failing arm
//@ mechanism: calls a panic lang item (`target: None`). extract/branching.rs used to push `cond`
//@ mechanism: into effects.assumptions (an effective PRECONDITION), so the assertion was assumed,
//@ mechanism: never proved. Creusot maps the panic call to Abort, which must be proved unreachable.
//@ accept-means: an assert! before the loop of a loop-bearing fn was neither assumed nor proved.
//@ WHY THE CONTRACT IS FALSE: `f(0)` panics before the loop.
//@ fixed-by: wp-s7 FRONT H step 1
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ < 100)]
pub fn f(n: u32) {
    assert!(n > 0);
    let mut i: u32 = 0;
    #[invariant(i@ <= n@)]
    while i < n {
        i += 1;
    }
}
