//@ expect: reject
//@ mechanism: a bare captured variable in an FnMut closure's own `#[ensures]` is rendered as
//@ mechanism: the PROPHECY of the capture's borrow — `Final(Deref(self.N))`, i.e. `^(self.N)`,
//@ mechanism: the referent's value when the closure's borrow RESOLVES — instead of the
//@ mechanism: capture's value at the end of THIS call, which is what a closure postcondition
//@ mechanism: means. Inside the closure's own verification nothing constrains that prophecy
//@ mechanism: symbol: the body's write `y = 5` resolves the CURRENT slot, so the goal
//@ mechanism: `^(self.0) == 100` is discharged against an unconstrained carrier and any value
//@ mechanism: the clause names is provable. `old(y)`, which maps to `Deref(self.N)` (the
//@ mechanism: current slot), is NOT affected — the two halves of the same clause are read in
//@ mechanism: two different environments.
//@ accept-means: an FnMut closure's postcondition over a mutated capture proves nothing about
//@ accept-means: the capture: `|| { y = 5; }` carries `#[ensures(y == 100)]` and verifies, so
//@ accept-means: any caller that later consumes that clause consumes a fact the body never
//@ accept-means: established.
//@ fixed-by: D-55
//@ WHY THE CONTRACT IS FALSE: the closure's only statement is `y = 5`, so after the single call
//@ WHY THE CONTRACT IS FALSE: `y == 5` and `driver()` returns 5 (main asserts exactly that).
//@ WHY THE CONTRACT IS FALSE: `y == 100` holds at no program point, in no execution. Nothing is
//@ WHY THE CONTRACT IS FALSE: `#[trusted]`.
//@ teeth: the closure postcondition path is NOT simply skipped, so the accept is specific to the
//@ teeth: capture rendering: the same file with `#[ensures(1 == 2)]` in place of
//@ teeth: `#[ensures(y == 100)]` is REFUTED — `trust-wp: driver::{closure#2} FAILED
//@ teeth: (postcondition)`, exit 1 — while `#[ensures(y == 100)]` reports `driver::{closure#2}
//@ teeth: verified`, exit 0, and so does `#[ensures(y == 5)]` (its control). A clause naming
//@ teeth: only `old(y)` (`#[ensures(old(y) == 100)]`) is withheld as unknown, exit 2: only the
//@ teeth: prophecy-rendered half is provable-for-free.
//@ also-verified: driver
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(true)]
#[ensures(true)]
pub fn driver() -> i32 {
    let mut y: i32 = 13;
    let mut c = #[requires(true)]
    #[ensures(y == 100)]
    || {
        y = 5;
    };
    c();
    y
}

pub fn main() {
    assert_eq!(driver(), 5);
}
