//@ expect: verify
//@ xfail: the price of D-136: two calls spelled `np` denote two definitions, so the parsed body, which holds both under one name, cannot be read as either; the body is refused. logic_fn_body_one_spelling_two_definitions.rs is the shape it closes.
//@ mechanism: control for logic_fn_callee_precondition_dropped_subterm_shared_spelling in the spelling the type-check vehicle does type-check, `f.postcondition((), np(y))`, under the caller's `#[requires(y > 0)]`: rustc resolves both `np` calls, the block's to `free` and the other to `needs_pos`, and the walk owes `needs_pos`'s precondition, which the caller's precondition gives.
//@ accept-means: n/a (control) — `np(y)` denotes `needs_pos` and `y > 0` wherever the caller may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
pub fn free(x: Int) -> Int {
    x
}

use crate::needs_pos as np;

#[logic]
#[requires(y > 0)]
#[ensures(true)]
pub fn caller<F: Fn() -> Int>(f: F, y: Int) -> bool {
    let a = {
        use crate::free as np;
        np(y)
    };
    f.postcondition((), a) == f.postcondition((), np(y))
}
