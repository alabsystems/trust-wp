//@ expect: reject
//@ mechanism: a store through a local `&mut` after a loop: the post-loop return walk skipped the
//@ mechanism: projected write `*r = 9` and returned `k`'s pre-loop value. A function with an
//@ mechanism: annotated loop also has its obligations rebuilt from block-scoped call walks, which
//@ mechanism: dropped the fail-closed `false` the primary walk's return sink pushes for a return
//@ mechanism: value read after such a store, so the function-level continuation proved the
//@ mechanism: postcondition over the pre-store value once the loop lane stated nothing.
//@ accept-means: `g()` returns 9, so `ensures(result == 0u32)` is FALSE, and trust-wp proved it.
//@ fixed-by: D-165 (the post-loop walk forgets a lent local, and `result` is unbound without a value) and D-223 (a loop function keeps the return sink's `false`)
//@ teeth: ACCEPTED at exit 0 before D-223, when this case was committed RED, and still ACCEPTED
//@ teeth: with the path-sensitive return walk alone (through the rebuilt obligations).
//@ verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 0u32)]
pub fn g() -> u32 {
    let mut k = 0u32;
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3 {
        i += 1;
    }
    let r = &mut k;
    *r = 9;
    k
}
