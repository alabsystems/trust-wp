//@ expect: reject
//@ mechanism: constructor-equality payload facts asserted at ENCODE time regardless of polarity —
//@ mechanism: encoding the goal `Err(3) == Err(0)` asserted `get0(Err 0) = 3` and `get0(Err 3) = 0`,
//@ mechanism: a contradictory base, so every goal over that equality "proved"
//@ fixed-by: cfff9b4 (s25 vacuous whole-value equality)
//@ accept-means: an enum-constructor equality in a goal again contributes unguarded premises
//@
//@ WHY THE ASSERTION IS FALSE: r is Err(3), not Err(0).
//@ teeth: VERIFIED — accepted (verified) on d9164f2, rejected with cfff9b4.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn res_lit_false() {
    let r: Result<i32, i32> = Err(3i32);
    proof_assert!(r == Err(0i32));
}
