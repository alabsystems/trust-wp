//@ expect: verify
//@ mechanism: a tuple match with no panic arm and no obligation site; the fail-closed demotion must not fire
//@ accept-means: n/a (control) — TRUE contract, must keep verifying
//@ fixed-by: wp-s40 diverging-callees (extraction fail-closed demotion)
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(p: (bool, bool)) -> u32 {
    match p { (false, false) => 1, _ => 2 }
}
