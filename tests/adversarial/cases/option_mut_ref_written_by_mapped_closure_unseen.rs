//@ expect: reject
//@ mechanism: the closure captures nothing; the `&mut` rides INSIDE the other by-value argument,
//@ mechanism: `Option<&mut u32>`, and the closure `Option::map` runs writes through it. Only a
//@ mechanism: top-level `&mut` argument gets a post-call value from the call lane, so the host's
//@ mechanism: proof reads `c` at 0 after the write.
//@ accept-means: `host` is reported `verified` although `host(true)` returns 5.
//@ WHY THE CONTRACT IS FALSE: `host(true)` maps `Some(&mut c)` through `*r = 5` and returns `c`.
//@ fixed-by: D-118: a `&mut` held below the top of an argument handed, beside a callable, to code
//@ fixed-by: trust-wp does not verify, leaves the host with no credit.
//@ teeth: ACCEPTED, exit 0, `host verified`, on the binary before D-118. After it `host`'s credit is
//@ teeth: withdrawn.
//@ also-verified: anchor
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == x@)]
pub fn anchor(x: u32) -> u32 {
    x
}

// FALSE: `host(true)` returns 5.
#[ensures(result@ == 0)]
pub fn host(b: bool) -> u32 {
    let mut c = 0u32;
    let o = if b { Some(&mut c) } else { None };
    let _ = o.map(|r| *r = 5);
    c
}
