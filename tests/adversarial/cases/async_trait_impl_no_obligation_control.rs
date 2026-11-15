//@ expect: verify
//@ xfail: the price of D-117, named: an `async fn` implementing a trait method is admitted as a trait impl method whether or not its body owes anything, and every admitted coroutine item is refused, so this impl, whose body is `0`, is refused. An impl method inherits its trait method's contract, so the item cannot be judged by its body alone.
//@ mechanism: over-refusal control for D-117: the no-obligation twin of async_trait_impl_overflow_never_examined, `0` for `x + u32::MAX`.
//@ fixed-by: n/a (open; closes when a lane verifies coroutine bodies, or when an impl that inherits no contract is admitted by its body's obligations alone)
//@ accept-means: n/a (control) — nothing in the crate is false; an XPASS means an async trait impl method with no obligation is no longer refused.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    async fn m(&self) -> u32;
}

pub struct S;
impl Tr for S {
    async fn m(&self) -> u32 {
        0
    }
}

#[ensures(result@ == 0)]
pub fn zero() -> u32 {
    0
}
