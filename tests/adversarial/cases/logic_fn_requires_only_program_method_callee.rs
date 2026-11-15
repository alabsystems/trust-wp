//@ expect: reject
//@ mechanism: a requires-only logic function is credited on its body goals, which never encoded the body: a method call the encoder refuses in the ensures lane (a program method it does not know) went unread. The credit's request now binds the body as the ensures lane does (`credited_on_body_goals`), so the encoder refuses it here too. Since D-136 the walk refuses the call first: rustc resolves `s.prog_get()` to the program function, which has a precondition.
//@ accept-means: a requires-only logic function that calls a program method outside its precondition is credited `verified` on a true assertion.
//@ WHY IT IS FALSE: at `s.v == 0` the body calls `s.prog_get()`, and `prog_get` requires `self.v@ > 0`.
//@ teeth: MEASURED ACCEPTED, exit 0, on the commit before D-119: `S::prog_get verified ✓` and the assertion `proved, not credited`; the call was never examined.
//@ fixed-by: D-119
//@ verdict: unknown
//@ refused-with: that denotes the program function `creusot_test::S::prog_get`, which has a precondition
//@ also-verified: S::prog_get
//@ also-verified-assertion: creusot_test::caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub v: i32,
}

impl S {
    #[requires(self.v@ > 0)]
    #[ensures(result == self.v)]
    pub fn prog_get(&self) -> i32 {
        self.v
    }
}

#[logic]
#[requires(true)]
pub fn caller(s: S) -> i32 {
    proof_assert!(true);
    s.prog_get()
}
