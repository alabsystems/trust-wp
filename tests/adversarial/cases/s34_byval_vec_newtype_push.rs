//@ expect: reject
//@ mechanism: stale by-value local after a field write (value kept its pre-write binding / entry-symbol write fact)
//@ fixed-by: s34 functional update of by-value locals on projected writes + owner havoc after field-borrow mutation
//@ accept-means: the returned local ignored the field write
//@
//@ WHY THE CONTRACT IS FALSE: `w.0.push(7)` makes the returned vector one longer.
//@ teeth: accepted (`verified`) on wp-s34 875b26cf; rejected after s34.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W(pub Vec<u64>);

#[requires(w.0@.len() < 100)]
#[ensures(result.0@.len() == w.0@.len())]
pub fn param_vec_newtype_push(mut w: W) -> W {
    w.0.push(7);
    w
}
