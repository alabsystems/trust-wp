//@ expect: reject
//@ mechanism: a trivial-body universal that holds only under a precondition, stated with none, must be refuted
//@ accept-means: trust-wp proved that adding an arbitrary u32 to every integer leaves it unchanged
//@ verdict: failed
//@ fn-failed: shift_id
//@ teeth: none — measured `shift_id FAILED ✗` both before and after the fix; kept as the false twin of `trivial_body_universal_requires_control`
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{logic::Int, prelude::*};

// WRONG without `#[requires(n@ == 0)]`: n = 1, i = 0 refutes it.
#[ensures(forall<i: Int> i + n@ == i)]
pub fn shift_id(n: u32) {}
