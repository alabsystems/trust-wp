//@ expect: verify
//@ xfail: the direct call `f(i)` of a safe const-block closure is charged with the precondition
//@ xfail: of `g`, the one non-capturing closure the body builds, so `pick` is refuted on `g`'s
//@ xfail: callee precondition (`i@ < 1`) although `f` runs no such call. Retiring it is the fix of
//@ xfail: its RED twin.
//@ mechanism: the TRUE twin of const_block_closure_direct_call_charged_with_sibling_closure_precondition:
//@ mechanism: the receiver census that hands `f(i)` the WP of the sibling closure `g` works in both
//@ mechanism: directions. Here `f` cannot panic and `g` calls `needs`, whose precondition is false
//@ mechanism: at `i >= 1`; the obligation charged at `f(i)` is `g`'s. A fix that closes the RED twin
//@ mechanism: by refusing every call whose receiver the census cannot pin must keep this
//@ mechanism: verifying through `f`'s own body WP, or it has traded a false accept for a lost credit.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — measured `pick FAILED ✗ (postcondition)` on `violated obligation #1: (i@ < 1)`,
//@ teeth: `needs`'s precondition instantiated at the argument of `f(i)`, on the binary with D-122
//@ teeth: and D-123.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 1)]
pub fn needs(x: usize) -> u32 {
    let _ = x;
    0
}

#[ensures(result@ == k@)]
pub fn pick(i: usize, k: u32) -> u32 {
    let g = |j: usize| needs(j);
    let _ = g(0);
    let f = const { |_j: usize| 0u32 };
    let _ = f(i);
    k
}
