//@ expect: reject
//@ mechanism: stale by-value local after a field write (value kept its pre-write binding / entry-symbol write fact)
//@ fixed-by: s34 functional update of by-value locals on projected writes + owner havoc after field-borrow mutation
//@ accept-means: the returned local ignored the field write
//@
//@ WHY THE CONTRACT IS FALSE: `p.0 = 5` then reading `p.0` returns 5.
//@ teeth: accepted (`verified`) on wp-s34 875b26cf; rejected after s34.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == 1u64)]
pub fn read_after_write() -> u64 {
    let mut p = (1u64, 2u64);
    p.0 = 5;
    p.0
}
