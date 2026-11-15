//@ expect: verify
//@ xfail: coverage. Under D-55 the capture owner's written field advances to a carrier the
//@ xfail: closure's `#[ensures(p.1@ == 1)]` says nothing about, so `result@ == 9` is UNPROVED —
//@ xfail: which is the correct state, not a false reject. It must NOT start verifying: that
//@ xfail: closure is contracted, its clause is silent about `p.0`, and anything that proves
//@ xfail: `result@ == 9` is reading a contracted closure's body — a new false-credit route.
//@ mechanism: the true twin of the adversarial case. `returns_post_value((1, 0))` returns 9
//@ mechanism: because the closure assigned 9 to `p.0`, so `result@ == 9` is a TRUE postcondition.
//@ mechanism: It is refuted today, which is what proves the capture owner is pinned to its entry
//@ mechanism: value rather than havocked: a havoc would leave this unknown, not failed.
//@ teeth: when this case was written it FAILED with a counterexample while its false twin
//@ teeth: verified — the entry symbol was being ASSERTED as the post-call value. It is now
//@ teeth: unproved instead. An XPASS is NOT the signal to look for; the signal was both
//@ teeth: adversarial twins rejecting while `_control` and `_written_field_control` verify.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(p.0@ == 1i32)]
#[ensures(result@ == 9i32)]
pub fn returns_post_value(mut p: (i32, i32)) -> i32 {
    let mut clos = #[ensures(p.1@ == 1i32)]
    || {
        p.0 = 9i32;
        p.1 = 1i32;
    };
    clos();
    p.0
}
