//@ expect: reject
//@ mechanism: `let mut c = flag(x); if c { r = big() }` before an annotated loop that writes `c = true`,
//@ mechanism: then `if c { r } else { 100 }` returned under `ensures(result@ >= 100)`. The premise's reach
//@ mechanism: condition reads `c`'s call result, which the function-level slice names by its site (D-244),
//@ mechanism: never by `c` at the loop's exit.
//@ accept-means: a function that returns 0 is credited with returning at least 100.
//@ WHY IT IS FALSE: `go(0)` returns 0.
//@ also-verified: big, flag
//@ teeth: rejected with D-243 and with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ >= 100)]
pub fn big() -> u32 { 100 }

#[ensures(result == (x@ > 7))]
pub fn flag(x: u32) -> bool { x > 7 }

#[ensures(result@ >= 100)]
pub fn go(x: u32) -> u32 {
    let mut c = flag(x);
    let mut r = 0u32;
    if c { r = big(); }
    let mut i = 0u32;
    #[invariant(i@ <= 3 && (i@ > 0 ==> c))]
    while i < 3 { c = true; i += 1; }
    if c { r } else { 100 }
}
