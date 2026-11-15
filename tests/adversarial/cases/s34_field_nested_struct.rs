//@ expect: reject
//@ mechanism: stale identity final value for a write through &mut to a field of a struct/newtype/tuple
//@ fixed-by: s34 value-carrier functional field updates + havoc of untracked writes
//@ accept-means: the borrow's final value ignored the field write (identity `^p == *p` premise)
//@
//@ WHY THE CONTRACT IS FALSE: `o.i.x += 1` makes `(^o).i.x == o.i.x + 1`.
//@ teeth: accepted (`verified`) on wp-campaign 212cb80 unless noted; rejected after s34.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct In {
    pub x: u64,
}

pub struct Out {
    pub i: In,
    pub k: u64,
}

#[requires(o.i.x < 100u64)]
#[ensures((^o).i.x == o.i.x)]
pub fn mut_o(o: &mut Out) {
    o.i.x += 1;
}
