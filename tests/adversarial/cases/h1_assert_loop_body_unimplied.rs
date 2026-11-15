//@ expect: reject
//@ mechanism: FRONT H step 1 — a plain `assert!` lowers to `SwitchInt(cond)` whose failing arm
//@ mechanism: calls a panic lang item (`target: None`). extract/branching.rs used to push `cond`
//@ mechanism: into effects.assumptions (an effective PRECONDITION), so the assertion was assumed,
//@ mechanism: never proved. Creusot maps the panic call to Abort, which must be proved unreachable.
//@ accept-means: the loop-body obligation collector dropped the panic arm of an in-loop assert!.
//@ WHY THE CONTRACT IS FALSE: `f(1)` enters the loop with i == 0 and panics.
//@ fixed-by: wp-s7 FRONT H step 1
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ < 100)]
pub fn f(n: u32) {
    let mut i: u32 = 0;
    #[invariant(i@ <= n@)]
    while i < n {
        assert!(i > 0);
        i += 1;
    }
}
