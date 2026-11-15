//@ expect: reject
//@ verdict: failed
//@ mechanism: the single-field twin of the two-field case. `Five` collapses under the
//@ mechanism: newtype identity `self.0 == self`, so this half also exercises the path
//@ mechanism: where field access on the argument is rewritten away before the obligation
//@ mechanism: reaches the solver.
//@ accept-means: the same free grant: `get` reasons from `inv(f)` while the call site
//@ accept-means: passes a value that breaks it.
//@ WHY THE CONTRACT IS FALSE: `caller` builds `Five(1)` and claims the result is 5.
//@ teeth: MEASURED as `unknown` (teeth lost) before the call-site obligation existed —
//@ teeth: rejected, but for no stated reason.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Five(pub i32);

impl Invariant for Five {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ == 5 }
    }
}

#[ensures(result@ == 5)]
pub fn get(f: Five) -> i32 {
    f.0
}

#[ensures(result@ == 5)]
pub fn caller() -> i32 {
    get(Five(1))
}
