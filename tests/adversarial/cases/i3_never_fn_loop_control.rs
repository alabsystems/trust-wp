//@ expect: verify
//@ mechanism: a -> ! fn that loops forever (partial correctness), caller keeps the surviving-path treatment (mirrors bug/nonreturning)
//@ accept-means: n/a (control) — TRUE contracts, must keep verifying
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn spin() -> ! {
    loop {}
}

#[allow(unreachable_code)]
#[ensures(!b)]
pub fn g(b: bool) {
    if b {
        spin();
    }
}
