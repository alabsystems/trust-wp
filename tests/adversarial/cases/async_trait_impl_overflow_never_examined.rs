//@ expect: reject
//@ mechanism: the trait-impl spelling of async_method_overflow_never_examined: an `async fn` implementing a contract-free trait method, whose coroutine body overflows.
//@ accept-means: an addition that overflows, in an async trait impl method, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: at `x == 1`, `x + u32::MAX` overflows.
//@ teeth: UNVERIFIED as a gate of D-117: rejected on the parent too, where a pass admits the async impl item as a trait impl method and D-106 refuses it (`<S as Tr>::m error`). At D-117 its coroutine body is refused as well (`<S as Tr>::m::{closure#0} error`).
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    async fn m(&self, x: u32) -> u32;
}

pub struct S;
impl Tr for S {
    async fn m(&self, x: u32) -> u32 {
        x + u32::MAX
    }
}

#[ensures(result@ == 0)]
pub fn zero() -> u32 {
    0
}
