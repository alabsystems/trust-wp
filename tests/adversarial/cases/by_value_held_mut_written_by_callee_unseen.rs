//@ expect: reject
//@ mechanism: a `&mut` held BELOW the top of an argument passed by value to a verified callee that writes
//@ mechanism: through it: a user struct with no `Drop` impl (`set(G(&mut c))`) and an `Option`
//@ mechanism: (`put(Some(&mut c))`). The call lane gives a post-call value only to a top-level `&mut`
//@ mechanism: argument (D-118 rule 4 says so), so the host reads `c` after the call at its value before
//@ mechanism: it. Neither callee's contract names the nested borrow's final value, and Creusot reads `c`
//@ mechanism: after the call as that prophecy, which nothing constrains. Found probing sideways from
//@ mechanism: D-140: the drop-glue spelling of this hand-off is closed there, the direct write is not.
//@ accept-means: a host is reported `verified` although the callee sets `c` to 5 through the borrow it was
//@ accept-means: handed.
//@ WHY THE CONTRACT IS FALSE: both hosts return 5.
//@ fixed-by: D-127: a call handed a value holding a borrow counts as a store through that borrow, so
//@ fixed-by: each host's read of `c` after the call is stale and fails closed. The call lane still
//@ fixed-by: gives `c` no post-call value; the refusal is what keeps the host from being credited.
//@ teeth: MEASURED as ACCEPTED, exit 0, `struct_arg` and `option_arg` `verified`, with and without
//@ teeth: D-140 on a tree without D-127; both `unknown` with D-127.
//@ also-verified: set, put
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

#[requires(true)]
pub fn set(g: G<'_>) {
    *g.0 = 5;
}

#[requires(true)]
pub fn put(o: Option<&mut u32>) {
    if let Some(r) = o {
        *r = 5;
    }
}

#[ensures(result@ == 0)]
pub fn struct_arg() -> u32 {
    let mut c = 0u32;
    set(G(&mut c));
    c
}

#[ensures(result@ == 0)]
pub fn option_arg() -> u32 {
    let mut c = 0u32;
    put(Some(&mut c));
    c
}
