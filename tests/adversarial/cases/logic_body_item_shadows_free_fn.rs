//@ expect: reject
//@ mechanism: a colliding free logic function named by a bare path (`k(x)`) was resolved through
//@ mechanism: the owner's MODULE (`use a::k`), although the owner's body declares its own `k`,
//@ mechanism: which is what the clause, type-checked at the head of that body, names.
//@ accept-means: the clause was read with `a::k` although the body's `k` shadows it.
//@ WHY THE CONTRACT IS FALSE: the body's `k(x)` is `x + 2`; `g(0)` returns 0.
//@ teeth: LIVE exit-0 false accept on the campaign tip 2e903433 (its logic-identity resolver,
//@ teeth: measured beside this commit's other changes); rejected by refusal once the body's item
//@ teeth: withholds the module's answer.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k(p: Int) -> Int { p }
}
pub mod b {
    use creusot_std::prelude::*;
    #[logic(open)]
    pub fn k(p: Int) -> Int { p + 1 }
}
use a::k;

#[ensures(result@ == k(x@))]
pub fn g(x: u32) -> u32 {
    #[logic(open)]
    fn k(p: Int) -> Int { p + 2 }
    x
}
