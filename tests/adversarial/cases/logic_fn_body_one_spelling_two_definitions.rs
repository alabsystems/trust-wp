//@ expect: reject
//@ mechanism: a logic body calls `k(y)` twice, once under a block-scoped `use crate::zero as k;` and once under the module's `use crate::one as k;`. rustc resolves the two calls to two definitions; the parsed body holds both under the one spelling `k`, which no pass resolved, so the encoder read both as one uninterpreted function and proved `k(y) == k(y)`. A spelling whose calls rustc resolves to two definitions makes the body misread (D-136). Found probing sideways from the resolution record.
//@ accept-means: `caller` claims `result`, returns `zero(y) == one(y)`, which is false, and the crate exits 0.
//@ WHY IT IS FALSE: the block's `k(y)` is `zero(y)`, 0, and the other is `one(y)`, 1.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`.
//@ fixed-by: D-136
//@ verdict: unknown
//@ refused-with: calls spelled `k` that rustc resolves to different definitions
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn zero(x: Int) -> Int {
    0
}

#[logic]
pub fn one(x: Int) -> Int {
    1
}

use crate::one as k;

#[logic]
#[ensures(result)]
pub fn caller(y: Int) -> bool {
    let a = {
        use crate::zero as k;
        k(y)
    };
    a == k(y)
}
