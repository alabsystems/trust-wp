//@ expect: verify
//@ mechanism: the TRUE twin of spec_fn_vec_with_capacity_overflow_std_spec_silent, identical but
//@ mechanism: for the `requires` bound: every capacity it admits fits in `isize::MAX` bytes. It pins
//@ mechanism: the over-refusal side of whatever closes that case — a `with_capacity` spec that
//@ mechanism: refuses every call is a blanket refusal, not a fix.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `g verified ✓`, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ <= 8)]
#[ensures(true)]
pub fn g(n: usize) -> usize {
    Vec::<u64>::with_capacity(n).capacity()
}
