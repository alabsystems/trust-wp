//@ expect: reject
//@ mechanism: a `&mut` held inside the POINTEE of a top-level `&mut` argument (`set(&mut g)` with `g =
//@ mechanism: G(&mut c)`). The call lane gives `g` a post-call value, but `c` is the pointee of `g.0`, one
//@ mechanism: level further down, and keeps its value before the call. The callee writes `*g.0 = 5`.
//@ accept-means: a host is reported `verified` although the callee sets `c` to 5 through the borrow inside
//@ accept-means: `g`.
//@ WHY THE CONTRACT IS FALSE: `host` returns 5.
//@ fixed-by: D-127: a call handed a value holding a borrow (here `&mut g`, which reaches `g.0`)
//@ fixed-by: counts as a store through that borrow, so `host`'s read of `c` is stale and fails closed.
//@ teeth: MEASURED as ACCEPTED, exit 0, `host verified`, with and without D-140 on a tree without
//@ teeth: D-127; `unknown` with D-127.
//@ also-verified: set
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

#[requires(true)]
pub fn set(g: &mut G<'_>) {
    *g.0 = 5;
}

#[ensures(result@ == 0)]
pub fn host() -> u32 {
    let mut c = 0u32;
    {
        let mut g = G(&mut c);
        set(&mut g);
    }
    c
}
