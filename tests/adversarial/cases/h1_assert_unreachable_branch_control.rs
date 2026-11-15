//@ expect: verify
//@ mechanism: FRONT H step 1 — a plain `assert!` lowers to `SwitchInt(cond)` whose failing arm
//@ mechanism: calls a panic lang item (`target: None`). extract/branching.rs used to push `cond`
//@ mechanism: into effects.assumptions (an effective PRECONDITION), so the assertion was assumed,
//@ mechanism: never proved. Creusot maps the panic call to Abort, which must be proved unreachable.
//@ accept-means: n/a (control) — both asserts sit under guards the precondition makes safe.
//@ fixed-by: wp-s7 FRONT H step 1
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x <= 0i32)]
#[ensures(result == x)]
pub fn f(x: i32) -> i32 {
    if x > 0 {
        assert!(false);
    }
    if x < -5 {
        assert!(x < 0);
    }
    x
}
