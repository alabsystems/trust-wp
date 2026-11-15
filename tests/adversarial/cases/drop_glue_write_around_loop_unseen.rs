//@ expect: reject
//@ mechanism: a writing guard dropped BEFORE a loop whose invariant claims the borrowed local unchanged,
//@ mechanism: and AFTER a loop, with and without an invariant, before the local is returned. The pre-loop
//@ mechanism: binding of `c`, and the post-loop return walk (`extract_post_loop_return`, which follows
//@ mechanism: only projection-free assignments), each read `c` at its value before the borrow.
//@ accept-means: a loop invariant's entry, or a postcondition read after a loop, is proved against the value
//@ accept-means: a writing drop has already replaced.
//@ WHY THE CONTRACT IS FALSE: `before_loop` enters its loop with `c == 5`; `after_loop` and `after_loop_invariant` return
//@ WHY THE CONTRACT IS FALSE: 5.
//@ fixed-by: D-140: the staleness summary counts a hand-off as a store to every local it reaches, which
//@ fixed-by: the loop-entry check reads, and the post-loop return walk re-binds those locals at the
//@ fixed-by: hand-off.
//@ teeth: MEASURED: with D-140's hand-off disabled all three hosts are ACCEPTED, exit 0, `verified`;
//@ teeth: with it `before_loop` and `after_loop` are `unknown` and `after_loop_invariant` is FAILED.
//@ teeth: The post-loop walk's fix is what moves `after_loop_invariant`: without it that host still
//@ teeth: verified with every other D-140 lane on.
//@ also-verified: <G<'_> as std::ops::Drop>::drop
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = 5;
    }
}

#[requires(n@ < 10)]
#[ensures(result@ == 0)]
pub fn before_loop(n: u32) -> u32 {
    let mut c = 0u32;
    {
        let _g = G(&mut c);
    }
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    #[invariant(c@ == 0)]
    while i < n {
        i += 1;
    }
    c
}

#[requires(n@ < 10)]
#[ensures(result@ == 0)]
pub fn after_loop(n: u32) -> u32 {
    let mut c = 0u32;
    let mut i = 0u32;
    while i < n {
        i += 1;
    }
    {
        let _g = G(&mut c);
    }
    c
}

#[requires(n@ < 10)]
#[ensures(result@ == 0)]
pub fn after_loop_invariant(n: u32) -> u32 {
    let mut c = 0u32;
    let mut i = 0u32;
    #[invariant(i@ <= n@)]
    while i < n {
        i += 1;
    }
    {
        let _g = G(&mut c);
    }
    c
}
