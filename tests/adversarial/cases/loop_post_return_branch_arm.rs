//@ expect: reject
//@ mechanism: the value a function returns after a loop was read by one pass over the blocks after
//@ mechanism: the loop exit, over one map of local values, which kept whichever assignment of the
//@ mechanism: return place it met last: after `if n > 5 { 1 } else { 2 }` it bound `result` to one
//@ mechanism: arm's value on every path, and the loop lane's postcondition check proved it.
//@ accept-means: `g(0)` returns 2, so `ensures(result == 1u32)` is FALSE, and trust-wp proved it.
//@ fixed-by: D-165 (the post-loop return walk is path-sensitive); this branch's own walk (D-223), dropped at the merge with D-165, closed it first
//@ teeth: ACCEPTED at exit 0 before D-223, when this case was committed RED.
//@ verdict: failed
//@ fn-failed: g
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 1u32)]
pub fn g(n: u32) -> u32 {
    let mut i = 0u32;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    if n > 5 { 1 } else { 2 }
}
