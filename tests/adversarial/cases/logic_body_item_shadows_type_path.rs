//@ expect: reject
//@ mechanism: a type-qualified logic call `T::k(..)` resolved its qualifier through the owner's
//@ mechanism: MODULE, although the owner's body declares its own `struct T` with its own `k`,
//@ mechanism: which is the `T` the clause names.
//@ accept-means: the clause was read with the module's `T::k` although the body's `T` shadows it.
//@ WHY THE CONTRACT IS FALSE: the body's `T::k(x)` is `x + 2`; `g(0)` returns 0.
//@ teeth: LIVE exit-0 false accept on the campaign tip 2e903433 (its logic-identity resolver,
//@ teeth: measured beside this commit's other changes); rejected by refusal once the body's item
//@ teeth: withholds the module's answer.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct T;
impl T {
    #[logic(open)]
    pub fn k(p: Int) -> Int { p }
}
pub struct U;
impl U {
    #[logic(open)]
    pub fn k(p: Int) -> Int { p + 1 }
}

#[ensures(result@ == T::k(x@))]
pub fn g(x: u32) -> u32 {
    struct T;
    impl T {
        #[logic(open)]
        pub fn k(p: Int) -> Int { p + 2 }
    }
    x
}
