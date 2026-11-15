//@ expect: verify
//@ mechanism: control: a check on the path to a trusted inert spin in a function with a loop was dropped by the block-slice walker (post-loop slice, loop-variable guard)
//@ accept-means: n/a (control) — `i - 1` with i == 5 cannot underflow; TRUE contract, must keep verifying
//@ fixed-by: wp-s40 diverging-callees-v3
//@ teeth: n/a — over-refusal control
//@ xfail: the flow-insensitive post-loop walker drops a guard over a loop-mutated variable (strict value stability), so the check is emitted unguarded — completeness cost, never soundness
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! { loop {} }
#[ensures(true)]
pub fn f(n: u32) { let mut i: u32 = 0; #[invariant(i <= n)] while i < n { i += 1; } if i == 5 { let _y = i - 1; spin() } }
