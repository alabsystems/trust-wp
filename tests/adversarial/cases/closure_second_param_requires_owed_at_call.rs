//@ expect: reject
//@ also-verified: h::{closure#1}
//@ mechanism: a closure of two parameters requires its SECOND parameter to be positive and is called
//@ mechanism: with (4, 0). The `requires` is owed over the tuple field the `Fn*` call passes for that
//@ mechanism: parameter.
//@ accept-means: a closure's precondition over its second parameter was not owed at a call that
//@ accept-means: violates it.
//@ WHY THE CONTRACT IS FALSE: `f(4, 0)` violates `b > 0`; the call's precondition is false.
//@ teeth: UNVERIFIED. Rejected at the head before D-180, where the `requires` over the unbound
//@ teeth: second parameter was owed as `false`, and with D-180 (`violated obligation #1: (0 > 0)`);
//@ teeth: a build binding the fields in reverse order rejects it too, on `h`'s own postcondition. No
//@ teeth: build that drops the `requires` silently was made.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == 0)]
pub fn h() -> u32 {
    let f = #[requires(b > 0u32)]
    #[ensures(result == b)]
    |_a: u32, b: u32| b;
    f(4, 0)
}
