//@ expect: verify
//@ xfail: the price of D-106, named: a contracted `async fn` and every coroutine body that owes anything (D-117) is REFUSED, not verified, so this TRUE assertion is refused exactly like the false one in its twin async_fn_body_assertion_never_examined, from which it differs in the literal alone. No lane models a coroutine's `Yield`/resume semantics, and Creusot verifies no coroutine either.
//@ mechanism: over-refusal control for the coroutine refusal
//@ fixed-by: n/a (open; closes when a lane verifies coroutine bodies)
//@ accept-means: n/a (control) — this assertion is TRUE; an XPASS means coroutine bodies are verified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
pub async fn ainc(x: u32) -> u32 {
    let y = x + 1;
    proof_assert!(y@ == x@ + 1);
    y
}
