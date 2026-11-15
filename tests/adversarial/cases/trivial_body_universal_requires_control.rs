//@ expect: verify
//@ mechanism: isolating twin of `trivial_body_universal_requires_dropped` — with the precondition it needs, the same universal is true and must be proved
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{logic::Int, prelude::*};

#[requires(n@ == 0)]
#[ensures(forall<i: Int> i + n@ == i)]
pub fn shift_id(n: u32) {}
