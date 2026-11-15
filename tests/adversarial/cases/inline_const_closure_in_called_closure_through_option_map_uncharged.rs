//@ expect: reject
//@ mechanism: inline_const_closure_index_through_option_map_uncharged one closure deeper: the host
//@ mechanism: calls a closure `f` it defines, and `f` hands `Option::map` a closure written in an
//@ mechanism: inline `const { }`. The host rests on what `f` hands over, so the const-owned closure
//@ mechanism: must be recorded as `f`'s hand-off.
//@ accept-means: `pick` is reported `verified` although `pick(Some(5), 0)` panics with "index out
//@ accept-means: of bounds".
//@ WHY THE CONTRACT IS FALSE: `pick(Some(5), 0)` runs `[1u32, 2][5]`.
//@ fixed-by: D-123: a closure's owner walk goes out through an inline or anonymous const, and a
//@ fixed-by: const-owned closure is keyed by the body around the const.
//@ teeth: MEASURED on the binary before D-123: `pick verified ✓` beside `pick::{closure#1} unknown`.
//@ teeth: After it `pick` is withdrawn: the closure it defines hands the const-owned closure to
//@ teeth: `Option::map`, and that closure was not verified.
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
pub fn pick(o: Option<usize>, k: u32) -> u32 {
    let f = |o: Option<usize>| o.map(const { |j: usize| [1u32, 2][j] });
    let _ = f(o);
    k
}
