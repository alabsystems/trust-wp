//@ expect: reject
//@ mechanism: mut-borrow structural shortcut gates read a mutation-continued param's identity
//@ mechanism: final_values entry (never asserted) as a fact, rewrote `^v` to `*v` and routed the
//@ mechanism: goal to the circular materialized-consequence proof
//@ fixed-by: cfff9b4 (s25 vacuous whole-value equality)
//@ accept-means: an un-advanced mutating call on a &mut param again leaves ^v == *v provable
//@
//@ WHY THE CONTRACT IS FALSE: extend appends w, so (^v)@ != (*v)@ whenever w is non-empty.
//@ teeth: VERIFIED — accepted (verified) on d9164f2, rejected (FAILED) with cfff9b4; the same
//@ teeth: happened for clear/truncate/Option::take and extend([1]).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures((^v)@ == (*v)@)]
pub fn extend_vec_false(v: &mut Vec<i32>, w: Vec<i32>) {
    v.extend(w);
}
