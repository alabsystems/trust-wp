//@ expect: reject
//@ mechanism: stale by-value local after a field write (value kept its pre-write binding / entry-symbol write fact)
//@ fixed-by: s34 functional update of by-value locals on projected writes + owner havoc after field-borrow mutation
//@ accept-means: the returned local ignored the field write
//@
//@ WHY THE CONTRACT IS FALSE: `p.a = 5` makes the returned struct `P { a: 5, b: 2 }`.
//@ teeth: accepted (`verified`) on wp-s34 875b26cf; rejected after s34.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P {
    pub a: u64,
    pub b: u64,
}

#[ensures(result.a == 1u64)]
pub fn local_struct() -> P {
    let mut p = P { a: 1, b: 2 };
    p.a = 5;
    p
}
