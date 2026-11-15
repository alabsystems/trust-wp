//@ expect: verify
//@ xfail: the price of D-136's counting: the parsed body holds two calls spelled `np` and the type-checked form one, because the vehicle does not type-check the flat `Fn` predicate the second sits in, so which `np` it is cannot be told and the body is refused, true as it is. The tuple spelling verifies (logic_fn_callee_precondition_dropped_subterm_typed_control.rs).
//@ mechanism: control for logic_fn_callee_precondition_dropped_subterm_shared_spelling, differing in the caller's `#[requires]` alone: every argument it admits is inside `needs_pos`'s precondition, so the call rustc never resolved is true whatever it denotes.
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
    f.postcondition((), a) == f.postcondition(np(y))
}
