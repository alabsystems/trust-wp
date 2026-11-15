//@ expect: reject
//@ mechanism: stale by-value local after a field write (value kept its pre-write binding / entry-symbol write fact)
//@ fixed-by: s34 functional update of by-value locals on projected writes + owner havoc after field-borrow mutation
//@ accept-means: the returned local ignored the field write
//@
//@ WHY THE CONTRACT IS FALSE: `t.0 += 1` on the by-value parameter makes `result.0 == t.0 + 1` (t is the entry value).
//@ teeth: NOT accepted on wp-s34 875b26cf (`errors`, stale value folded); regression guard for the functional update.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(t.0 < 100u64)]
#[ensures(result.0 == t.0)]
pub fn param_tuple(mut t: (u64, u64)) -> (u64, u64) {
    t.0 += 1;
    t
}
