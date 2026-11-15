//@ expect: reject
//@ verdict: failed
//@ mechanism: a recursive function's own body extraction runs against a table into which
//@ mechanism: its OWN contract is injected, so the self-call resolves. That injected entry
//@ mechanism: overrides the table's, and it was built with an empty synthesized
//@ mechanism: `inv(param)` vector, so the self-call was the one call site in the crate
//@ mechanism: that owed nothing while the body held the premise.
//@ accept-means: a function can launder a value that breaks its parameter's type invariant
//@ accept-means: through a call to ITSELF and keep its postcondition.
//@ WHY THE CONTRACT IS FALSE: at `n = 1` the function really returns 1 + 1 = 2, and the
//@ WHY THE CONTRACT IS FALSE: contract claims 10 for every `n`.
//@ teeth: MEASURED as ACCEPTED, exit 0, "1 verified, 0 failed".
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Sum10 {
    pub a: i32,
    pub b: i32,
}

impl Invariant for Sum10 {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ == 10 }
    }
}

#[ensures(result@ == 10)]
pub fn total(s: Sum10, n: u32) -> i32 {
    if n == 0 {
        s.a + s.b
    } else {
        total(Sum10 { a: 1, b: 1 }, 0)
    }
}
