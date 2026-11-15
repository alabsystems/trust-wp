//@ expect: verify
//@ mechanism: control: a postcondition over a destructured parameter's binding, `result == a + 1u32`.
//@ mechanism: The clause is rewritten over the positional parameter's projection, a text no type
//@ mechanism: check reads, so D-232 reads it by syntax alone.
//@ WHY THE CONTRACT IS TRUE: a < 100, so a + 1 does not wrap and the body returns it.
//@ xfail: the rewritten clause's `+` on `u32` is refused (D-232).
//@ xfail-verdict: unknown
//@ teeth: n/a, a control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a < 100u32)]
#[ensures(result == a + 1u32)]
pub fn destructured((a, b): (u32, u32)) -> u32 {
    a + 1
}
