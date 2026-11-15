//@ expect: reject
//@ mechanism: stale identity final value for a write through &mut to a field of a struct/newtype/tuple
//@ fixed-by: s34 value-carrier functional field updates + havoc of untracked writes
//@ accept-means: the borrow's final value ignored the field write (identity `^p == *p` premise)
//@
//@ WHY THE CONTRACT IS FALSE: `w.v.push(1)` grows the field vector.
//@ teeth: accepted (`verified`) on wp-campaign 212cb80 unless noted; rejected after s34.
//@ teeth: rejected on 212cb80 too (the call through the FIELD reborrow was not marked
//@ teeth: mutation-continued, but the Seq view mismatch hid it); kept as a shape gate.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct V {
    pub v: Vec<u64>,
}

#[ensures((^w).v@ == w.v@)]
pub fn push_v(w: &mut V) {
    w.v.push(1);
}
