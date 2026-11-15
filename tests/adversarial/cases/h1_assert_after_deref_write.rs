//@ expect: reject
//@ mechanism: FRONT H step 1 — a plain `assert!` lowers to `SwitchInt(cond)` whose failing arm
//@ mechanism: calls a panic lang item (`target: None`). extract/branching.rs used to push `cond`
//@ mechanism: into effects.assumptions (an effective PRECONDITION), so the assertion was assumed,
//@ mechanism: never proved. Creusot maps the panic call to Abort, which must be proved unreachable.
//@ accept-means: the assert condition was read against the entry value of `*x`, not the written one.
//@ WHY THE CONTRACT IS FALSE: `*x = -1` then `assert!(*x > 0)` panics on every run.
//@ fixed-by: wp-s7 FRONT H step 1
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(*x > 0i32)]
pub fn f(x: &mut i32) {
    *x = -1;
    assert!(*x > 0);
}
