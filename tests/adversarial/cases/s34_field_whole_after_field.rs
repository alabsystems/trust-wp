//@ expect: reject
//@ mechanism: stale identity final value for a write through &mut to a field of a struct/newtype/tuple
//@ fixed-by: s34 value-carrier functional field updates + havoc of untracked writes
//@ accept-means: the borrow's final value ignored the field write (identity `^p == *p` premise)
//@
//@ WHY THE CONTRACT IS FALSE: the final whole write `*t = (1, 2)` overrides `t.0 = 7`, so `(^t).0 == 1`.
//@ teeth: accepted (`verified`) on wp-campaign 212cb80 unless noted; rejected after s34.
//@ teeth: on 212cb80 the per-field reconstruction over the entry value produced `(7, t.1)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((^t).0 == 7u64)]
pub fn whole_after_field(t: &mut (u64, u64)) {
    t.0 = 7;
    *t = (1, 2);
}
