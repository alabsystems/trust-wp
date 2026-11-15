//@ expect: reject
//@ mechanism: stale identity final value for a write through &mut to a field of a struct/newtype/tuple
//@ fixed-by: s34 value-carrier functional field updates + havoc of untracked writes
//@ accept-means: the borrow's final value ignored the field write (identity `^p == *p` premise)
//@
//@ WHY THE CONTRACT IS FALSE: when `c` holds, `(^t).0 == 7` which differs from `t.0 == 0`.
//@ teeth: accepted (`verified`) on wp-campaign 212cb80 unless noted; rejected after s34.
//@ teeth: on 212cb80 the branch merge produced `Ite(c, *t, *t)`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(t.0 == 0u64)]
#[ensures((^t).0 == t.0)]
pub fn branch(t: &mut (u64, u64), c: bool) {
    if c {
        t.0 = 7;
    }
}
