//@ expect: reject
//@ mechanism: `let mut b = small(); let a = if c { b } else { 5 }` before an annotated loop that writes `b
//@ mechanism: = 50`, then `if c { b } else { a }` returned under `ensures(result@ < 10)`. A loop-entry
//@ mechanism: value of `a` reading `b` must not be stated past a loop that changes `b` (D-244 keeps D-243's
//@ mechanism: rule for every name a value reads).
//@ accept-means: a function that returns 50 is credited with returning less than 10.
//@ WHY IT IS FALSE: `go(true, 1)` returns 50.
//@ also-verified: small
//@ teeth: rejected with D-243 and with D-244.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ < 10)]
pub fn small() -> u32 { 3 }

#[requires(n@ < 100)]
#[ensures(result@ < 10)]
pub fn go(c: bool, n: u32) -> u32 {
    let mut b = small();
    let a = if c { b } else { 5u32 };
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n { b = 50; i += 1; }
    if c { b } else { a }
}
