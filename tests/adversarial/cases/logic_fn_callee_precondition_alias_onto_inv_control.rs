//@ expect: verify
//@ mechanism: control for logic_fn_callee_precondition_alias_onto_inv, differing in the renaming `use` alone: `inv(y)` is the prelude's type invariant, which owes nothing, so a fix that refuses a rebound `inv` must still verify this.
//@ accept-means: n/a (control) — `inv(y)` is the builtin invariant of an `Int` and owes nothing.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos_b(x: Int) -> bool {
    x > 5
}

#[logic]
#[ensures(true)]
pub fn caller(y: Int) -> bool {
    inv(y)
}
