//@ expect: verify
//@ mechanism: the TRUE disjoint-capture shape the adversarial case perturbs — the closure writes
//@ mechanism: only `p.1`, so `p.0` really does keep its entry value and returning it really does
//@ mechanism: satisfy `result@ == 1`. It must keep verifying: a fix that advances the capture
//@ mechanism: owner by forgetting it wholesale would break this, and the correct fix advances
//@ mechanism: only what the closure actually wrote.
//@ teeth: verifies on this tree (exit 0). It is the control the adversarial case is a one-line
//@ teeth: perturbation of: adding `p.0 = 9;` to the closure body is the only difference, and
//@ teeth: that difference does not change the verdict — which is the finding.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(p.0@ == 1i32)]
#[ensures(result@ == 1i32)]
pub fn disjoint_capture_untouched_field(mut p: (i32, i32)) -> i32 {
    let mut clos = #[ensures(p.1@ == 1i32)]
    || {
        p.1 = 1i32;
    };
    clos();
    p.0
}
