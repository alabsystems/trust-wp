//@ expect: reject
//@ mechanism: the escape class D-118 closes, with the closure written inside an inline `const { }`
//@ mechanism: block. The escape scan skips a closure whose owner is not program code, reading
//@ mechanism: `is_program_host` as "trusted or specification", but that walk returns `false` for
//@ mechanism: ANY owner other than a fn, a method or a closure. An inline const is such an owner, so
//@ mechanism: the closure handed to `Option::map` is recorded as nothing: it is no target, and the
//@ mechanism: host rests on no verdict. The closure is ordinary runtime code; only its construction
//@ mechanism: is const-evaluated.
//@ accept-means: `pick` is reported `verified` although `pick(Some(5), 0)` panics with "index out of
//@ accept-means: bounds" inside the closure `Option::map` calls.
//@ WHY THE CONTRACT IS FALSE: `pick(Some(5), 0)` indexes a two-element array at 5; compiled and run
//@ WHY THE CONTRACT IS FALSE: as a plain program it panics.
//@ fixed-by: D-123: a closure's owner walk goes out through an inline or anonymous const to the
//@ fixed-by: code around it, so the closure is an escaping target and `pick` rests on its verdict.
//@ teeth: MEASURED: ACCEPTED, exit 0, `pick verified`, on the binary before D-123; after it the
//@ teeth: closure `pick::{constant#0}::{closure#0}` is not proved and `pick`'s credit is withdrawn.
//@ teeth: The isolating pair is inline_const_closure_guarded_index_through_option_map_control, the
//@ teeth: same closure with its index guarded: `pick verified ✓` on both binaries, and after D-123
//@ teeth: the closure is a target and verifies too.
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
    let _ = o.map(const { |j: usize| [1u32, 2][j] });
    k
}
