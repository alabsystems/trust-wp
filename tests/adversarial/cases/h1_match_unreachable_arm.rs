//@ expect: reject
//@ mechanism: FRONT H step 1 — a plain `assert!` lowers to `SwitchInt(cond)` whose failing arm
//@ mechanism: calls a panic lang item (`target: None`). extract/branching.rs used to push `cond`
//@ mechanism: into effects.assumptions (an effective PRECONDITION), so the assertion was assumed,
//@ mechanism: never proved. Creusot maps the panic call to Abort, which must be proved unreachable.
//@ accept-means: an `unreachable!()` match arm (int/enum switch) was assumed unreachable.
//@ WHY THE CONTRACT IS FALSE: `f(None)` panics.
//@ fixed-by: wp-s7 FRONT H step 1
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0i32)]
pub fn f(o: Option<i32>) -> i32 {
    match o {
        Some(_) => 0,
        None => unreachable!(),
    }
}
