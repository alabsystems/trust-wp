//@ expect: reject
//@ mechanism: an operator over two `f32` literals is folded on the host in single precision:
//@ mechanism: `16777216.0f32 + 1.0f32` rounds back to `16777216.0f32`, so the comparison is `true`.
//@ mechanism: A fold in double precision, or over the reals, keeps `16777217.0` and answers `false`.
//@ accept-means: `absorbs()` returns `true`; an accept claims it returns `false`.
//@ fixed-by: D-215
//@ teeth: ACCEPTED (`absorbs verified`) on the campaign tip before D-215, which added the literals as
//@ teeth: real numbers; rejected after.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == false)]
pub fn absorbs() -> bool {
    16777216.0f32 + 1.0f32 == 16777216.0f32
}
