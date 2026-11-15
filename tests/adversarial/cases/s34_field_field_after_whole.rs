//@ expect: reject
//@ mechanism: stale identity final value for a write through &mut to a field of a struct/newtype/tuple
//@ fixed-by: s34 value-carrier functional field updates + havoc of untracked writes
//@ accept-means: the borrow's final value ignored the field write (identity `^p == *p` premise)
//@
//@ WHY THE CONTRACT IS FALSE: after `*t = (1, 2); t.0 = 7` the second field is 2, not the entry `t.1`.
//@ teeth: accepted (`verified`) on wp-campaign 212cb80 unless noted; rejected after s34.
//@ teeth: on 212cb80 the reconstruction produced `(7, t.1)` (entry second field).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((^t).1 == t.1)]
pub fn field_after_whole(t: &mut (u64, u64)) {
    *t = (1, 2);
    t.0 = 7;
}
