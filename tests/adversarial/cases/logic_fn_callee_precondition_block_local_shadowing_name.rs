//@ expect: reject
//@ mechanism: the precondition spelling of logic_fn_body_block_local_name_shadowing_module_name: a block declares a logic function `k` with `#[requires(x > 0)]` and the crate root a `k` with none. Rust resolves `inner`'s `k(y)` to the block's `k`. The identity pass names the call by the root's `k`, so the callee-precondition walk owed the root's precondition, which is nothing. The body's type-checked form resolves the call to the block's `k`, so the parsed call's id has no counterpart there and the body is refused (D-136). Found probing sideways from D-120.
//@ accept-means: a logic function that calls another outside its precondition is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `y == 0` `inner` calls the block's `k(0)`, which requires `x > 0`; Creusot's vc for `inner` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::host::inner verified ✓`.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
pub fn k(x: Int) -> Int {
    x
}

pub fn host() -> u32 {
    #[logic]
    #[requires(x > 0)]
    fn k(x: Int) -> Int {
        x
    }

    #[logic]
    #[ensures(true)]
    fn inner(y: Int) -> Int {
        k(y)
    }

    0
}
