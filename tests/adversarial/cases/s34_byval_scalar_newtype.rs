//@ expect: reject
//@ mechanism: stale by-value local after a field write (value kept its pre-write binding / entry-symbol write fact)
//@ fixed-by: s34 functional update of by-value locals on projected writes + owner havoc after field-borrow mutation
//@ accept-means: the returned local ignored the field write
//@
//@ WHY THE CONTRACT IS FALSE: `s.0 += 1` on the by-value newtype parameter makes `result.0 == s.0 + 1`.
//@ teeth: accepted (`verified`) on wp-s34 875b26cf; rejected after s34.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S(pub u64);

#[requires(s.0 < 100u64)]
#[ensures(result.0 == s.0)]
pub fn param_scalar_newtype(mut s: S) -> S {
    s.0 += 1;
    s
}
