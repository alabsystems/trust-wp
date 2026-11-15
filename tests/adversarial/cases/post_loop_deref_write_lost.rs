//@ expect: reject
//@ mechanism: a write through a local `&mut` borrow AFTER a loop that carries an invariant: `let r = &mut
//@ mechanism: c; *r = 5; c`. The function-level result is the post-loop return walk's
//@ mechanism: (`extract_post_loop_return`), which follows only projection-free assignments, so `c` is
//@ mechanism: returned at its pre-loop value. The same write before any loop is refused by the return
//@ mechanism: sink's stale-read guard. Found probing D-140's post-loop spelling; not a drop.
//@ accept-means: a postcondition read after a loop is proved against a local's value before a write through a
//@ accept-means: borrow of it.
//@ WHY THE CONTRACT IS FALSE: `host` returns 5.
//@ fixed-by: D-165
//@ teeth: LIVE: ACCEPTED, exit 0, `host verified`, with and without D-140, and at the campaign tip
//@ teeth: D-165 branched from. At D-165 the walk forgets `c` at the loan `r = &mut c`, so `host` is
//@ teeth: `unknown (incomplete loop: no single post-loop return value)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ < 10)]
#[ensures(result@ == 0)]
pub fn host(n: u32) -> u32 {
    let mut c = 0u32;
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n {
        i += 1;
    }
    let r = &mut c;
    *r = 5;
    c
}
