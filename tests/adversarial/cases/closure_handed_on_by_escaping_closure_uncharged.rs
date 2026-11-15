//@ expect: reject
//@ mechanism: an escaping closure that has no obligation of its own hands ANOTHER closure to a
//@ mechanism: combinator. The outer closure owes nothing itself (it is not a target), so the host's
//@ mechanism: credit must rest on what the outer closure hands over in turn: the inner closure calls
//@ mechanism: `needs_nonzero` on every slice element.
//@ accept-means: `pick` is reported `verified` although `pick(Some(1), &[0])` divides by zero in
//@ accept-means: `needs_nonzero`, two combinators deep.
//@ fixed-by: D-118
//@ teeth: UNVERIFIED as a live accept: on the binary before D-118 `pick` is already `unknown`,
//@ teeth: demoted on an opaque-call assumption for the inner `for_each`, and no closure is
//@ teeth: examined. After it the inner closure is refuted on `needs_nonzero`'s precondition. The
//@ teeth: case pins that the hand-off two combinators deep is still found once that demotion goes.
//@ also-verified: needs_nonzero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ != 0)]
#[ensures(result@ == 10 / x@)]
pub fn needs_nonzero(x: u32) -> u32 {
    10 / x
}

// FALSE: `pick(Some(1), &[0])` calls `needs_nonzero(0)`.
#[ensures(result@ == 1)]
pub fn pick(o: Option<u32>, v: &[u32]) -> u32 {
    let _ = o.map(|_k| {
        v.iter().for_each(|&x| {
            needs_nonzero(x);
        })
    });
    1
}
