//@ expect: verify
//@ mechanism: one NaN, both meanings of `==`: in the program IEEE-754 `n == n` is false, and in an
//@ mechanism: assertion logical `n == n` is true. A model that reads either as the other fails one of them.
//@ accept-means: n/a (control) — `program_nan_unequal` returns `false` and the assertion is reflexivity.
//@ fixed-by: n/a (control)
//@ teeth: `program_nan_unequal` failed on the campaign tip before D-215 (the reals have no NaN);
//@ teeth: both verify after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(!result)]
pub fn program_nan_unequal() -> bool {
    let n = 0.0f64 / 0.0;
    n == n
}

#[ensures(true)]
pub fn assertion_nan_equal() {
    let n = 0.0f64 / 0.0;
    proof_assert!(n == n);
}
