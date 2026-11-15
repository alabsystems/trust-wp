//@ expect: reject
//@ mechanism: a coroutine whose only obligation is a type invariant: the result of `mk`'s body is a `Small` that breaks `x < 3`. The same function without `async` is discovered by its invariant-bearing signature and refuted; the `async fn` item's signature returns an opaque future, and its coroutine body holds no call, no assert and no arithmetic, so only a check of the body's own local types admits it.
//@ accept-means: a value that breaks its type's invariant, produced by an `async fn`, is examined by no pass and the run is clean.
//@ WHY IT IS FALSE: `Small { x: 5 }` violates `self.x@ < 3`, which every `Small` a program function returns owes.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `zero verified ✓` and no line for the coroutine; REFUSED at the fix (`mk::{closure#0} error: ... refused instead of credited`). The sync twin (the same file without `async`) was already rejected on the parent commit (`failed`).
//@ fixed-by: D-117 — `discover_coroutine_obligation_bodies` makes every coroutine body that owes anything a target of the contract loop's coroutine refusal
//@ verdict: unknown
//@ refused-with: which trust-wp does not verify; refused instead of credited
//@ also-verified: zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Small {
    pub x: u32,
}

impl Invariant for Small {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.x@ < 3 }
    }
}

pub async fn mk() -> Small {
    Small { x: 5 }
}

#[ensures(result@ == 0)]
pub fn zero() -> u32 {
    0
}
