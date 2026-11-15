//@ expect: reject
//@ mechanism: a const-block closure called directly by the body around it (D-123 makes it program
//@ mechanism: code of that body) owes its precondition at the call, which D-54 resolves to the
//@ mechanism: closure's body WP. The receiver of `f(i)` is the closure's environment, and a
//@ mechanism: non-capturing closure's environment is the unit term `__trust_wp_tuple0()`. That term
//@ mechanism: names no closure, so `rewrite_contract_free_closure_preconditions` identifies it by
//@ mechanism: its capture count through `collect_sole_env_owners`, a census of the closure
//@ mechanism: AGGREGATES the body builds. A const-block closure is not built by the body (its value
//@ mechanism: is a constant), so it is not counted, and `g`, the one non-capturing aggregate, is
//@ mechanism: taken as the receiver: `f(i)` is charged with `g`'s body WP (`true`) instead of its
//@ mechanism: own (`i < 2`). Without `g` the obligation stays unresolved and `pick` is refuted; with
//@ mechanism: `g` capturing one variable (another capture count) it is `unknown`; with `f` an
//@ mechanism: ordinary `let f = |j| ..` (an aggregate the census counts, so capture count 0 is no
//@ mechanism: longer sole) it is refuted. The substitution is visible in the other direction too:
//@ mechanism: a safe const-block closure beside `let g = |j: usize| needs(j)` (`needs` requires
//@ mechanism: `x@ < 1`) is FAILED on `violated obligation #1: (i@ < 1)`, `g`'s precondition.
//@ fixed-by: OPEN — committed RED rather than hidden. The grant (the WP of the closure the census
//@ fixed-by: picked) and the obligation (the closure that runs) are two closures. Closing it means the
//@ fixed-by: receiver is identified by the closure the call's type names, or the census counts every
//@ fixed-by: closure value the body can hold (its constants included), so a capture count shared
//@ fixed-by: with a const-block closure is no longer sole.
//@ accept-means: `pick` is reported `verified` although `pick(5, 0)` panics with "index out of
//@ accept-means: bounds" inside the const-block closure it calls.
//@ WHY THE CONTRACT IS FALSE: `pick(5, 0)` calls the const-block closure at 5, which indexes a
//@ WHY THE CONTRACT IS FALSE: two-element array; compiled and run as a plain program it panics.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`pick verified ✓`), with `g` declared before the call and
//@ teeth: after it alike, on the binary with D-122 and D-123 and on the binary before them.
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

#[ensures(result@ == k@)]
pub fn pick(i: usize, k: u32) -> u32 {
    let g = |_j: usize| 0u32;
    let _ = g(0);
    let f = const { |j: usize| [1u32, 2][j] };
    let _ = f(i);
    k
}
