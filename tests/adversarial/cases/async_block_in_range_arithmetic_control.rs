//@ expect: verify
//@ xfail: the price of D-117, named: a coroutine body that owes any goal is REFUSED, not verified, so this in-range addition is refused exactly like the overflowing one in its twin async_block_overflow_never_examined, from which it differs in the addend alone. Creusot verifies no coroutine either.
//@ mechanism: the in-range twin of async_block_overflow_never_examined: `x + 1` under `x < 100` cannot overflow, yet the block owes the goal and no lane verifies a coroutine, so it is refused exactly like the overflowing one. The pair shows the refusal is not a solver verdict.
//@ fixed-by: n/a (open; closes when a lane verifies coroutine bodies)
//@ accept-means: n/a (control) — the addition is in range; an XPASS means coroutine bodies are verified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(0 < x@ && x@ < 100)]
#[ensures(result@ == x@)]
pub fn f(x: u32) -> u32 {
    let _fut = async move { x + 1 };
    x
}
