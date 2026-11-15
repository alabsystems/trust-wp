//@ expect: reject
//@ verdict: failed
//@ fn-failed: bump
//@ mechanism: the view rule of D-118 identifies `(*x)@` with `x@` for a variable that is not `&mut`
//@ mechanism: (the encoder already reads `*x` of such a variable AS `x`). A rule that identified it
//@ mechanism: with anything else would let this off-by-one postcondition through.
//@ accept-means: `bump(&1)` returns 1, not 2, and is credited.
//@ fixed-by: D-118
//@ teeth: refuted before and after D-118.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == (*x)@ + 1)]
pub fn bump(x: &u32) -> u32 {
    *x
}
