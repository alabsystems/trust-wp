//@ expect: reject
//@ mechanism: an `async fn`'s body is lowered into a coroutine, a body of its own; the `async fn` item's MIR only builds that coroutine. The contract loop verifies the item, whose VC has nothing to prove, and the in-function assertion pass walks the item's MIR alone, so the `proof_assert!` in the coroutine is examined by no pass; D-87 then settles the item's credit on an empty assertion tally. It is not only the assertion: an overflowing `x + u32::MAX` in an `async fn` body is accepted the same way. Creusot does not verify coroutines at all (its MIR translation treats `Yield` as unreachable), so an accept here is a verdict on code nobody examined.
//@ accept-means: an `async fn` whose own assertion is false for every argument is credited `verified`, and the crate exits 0.
//@ WHY THE ASSERTION IS FALSE: `y` is `x + 1`, never `x + 2`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-87's fold and before it: `ainc verified ✓` and every proof_assert counter zero on the wire.
//@ fixed-by: D-106 — REFUSED, not examined: `is_coroutine_body` makes the contract loop refuse the `async fn` item and the standalone pass refuse each assertion of the coroutine body, which discovery now admits
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
pub async fn ainc(x: u32) -> u32 {
    let y = x + 1;
    proof_assert!(y@ == x@ + 2);
    y
}
