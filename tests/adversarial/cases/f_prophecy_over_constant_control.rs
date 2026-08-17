//@ expect: verify
//@ mechanism: Final-collapse guard, CONSTANT-carrier arm — over-refusal control.
//@ mechanism: The refusal is scoped to `Final` over a constant. `Deref` over a constant is
//@ mechanism: faithful (a literal in wrapper position already IS the referent's value) and must
//@ mechanism: keep collapsing, and a borrow that is never mutated through must stay provable.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — this contract is TRUE. A REJECT here means the constant-carrier
//@ accept-means: refusal is over-broad and is eating the `Deref`-over-literal lane with it.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

/// TRUE contract: the borrow is only read through, so `x` keeps its value.
#[ensures(result@ == 3)]
pub fn read_only_borrow_of_constant() -> i32 {
    let mut x = 3i32;
    let r = &mut x;
    let v = *r;
    return v;
}
