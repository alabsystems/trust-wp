//@ expect: reject
//@ also-verified: h::{closure#2}
//@ mechanism: a closure of two parameters, the first a `&mut`, writes through it; its `ensures`
//@ mechanism: names only the value parameter. A closure's call advances only its receiver, never a
//@ mechanism: `&mut` inside the argument tuple, so granting that clause at the call keeps the
//@ mechanism: caller's `x` at its value before the call.
//@ accept-means: a clause of a closure with a `&mut` parameter was granted at a call that does not
//@ accept-means: advance what that parameter borrows, and the write through it was lost.
//@ WHY THE CONTRACT IS FALSE: `f(&mut x, 3)` stores 3 in `x`, so `h()` returns 3, not 0. The
//@ WHY THE CONTRACT IS FALSE: closure's own contract is true and is credited on purpose.
//@ teeth: ACCEPTED (exit 0, `h verified`) on a build of D-180 without its `&mut` restriction, which
//@ teeth: binds `b` to 3 and never advances `x`. Rejected at the head before D-180 (`b` unbound) and
//@ teeth: with it (no parameter bound; `h` unknown, failing closed).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == 0)]
pub fn h() -> u32 {
    let mut x = 0u32;
    let f = #[ensures(result == b)] |a: &mut u32, b: u32| -> u32 {
        *a = b;
        b
    };
    let _ = f(&mut x, 3);
    x
}
