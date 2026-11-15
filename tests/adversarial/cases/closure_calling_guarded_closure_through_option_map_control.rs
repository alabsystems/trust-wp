//@ expect: verify
//@ xfail: D-118's price. The called closure `f` reads the slice through the escaping closure's
//@ xfail: environment, and the call lane leaves such a callee's precondition opaque (`precondition(j)`
//@ xfail: over `self.0`) instead of reading `f`'s body WP, so the escaping closure is refuted although
//@ xfail: `f`'s precondition is `true`.
//@ mechanism: the isolating control for closure_calling_closure_through_option_map_uncharged: the SAME
//@ mechanism: two hosts, each `f` guarding its index by the slice's length, so its precondition (its
//@ mechanism: body's WP) is `true` and each escaping closure verifies under `requires true` once the
//@ mechanism: call lane reads that WP through a capture.
//@ accept-means: n/a (control) — every index is guarded.
//@ fixed-by: n/a (control)
//@ teeth: control — both hosts `verified` on the binary before D-118, where no closure was examined;
//@ teeth: refused after it on the opaque precondition named above.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 1)]
pub fn pick(o: Option<usize>, w: &[u32]) -> u32 {
    let f = |j: usize| if j < w.len() { w[j] } else { 0 };
    let _ = o.map(|j| f(j));
    1
}

#[ensures(result@ == 1)]
pub fn pick_inner(o: Option<usize>, w: &[u32]) -> u32 {
    let _ = o.map(|j| {
        let f = |k: usize| if k < w.len() { w[k] } else { 0 };
        f(j)
    });
    1
}
