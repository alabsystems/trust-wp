//@ expect: verify
//@ mechanism: control for the s68_handback_redirect_* rejects: a GENUINELY fresh reborrow. `zero(&mut x)`
//@ mechanism: lends `x` itself, `x` is borrowed nowhere else and `zero`'s result carries no borrow, so at
//@ mechanism: the return `x == ^p == 0` is a literal consequence of the contract and `x + 1` is in range.
//@ mechanism: The 8a909ade refusal must not touch this: the reborrowed local `x` is the LENT place, not
//@ mechanism: a local whose value the handback reads off a definition.
//@ fixed-by: n/a — over-refusal guard for wp-s68 v2 8a909ade.
//@ teeth: control - must keep verifying. Verified on both sides of the A/B (e552908e and
//@ teeth: 8a909ade); the instrumented
//@ teeth: driver printed `param p <- caller local x through_deref=false` on both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^p == 0)]
fn zero(p: &mut i32) {
    *p = 0;
}

pub fn probe_fresh_direct(x0: i32) -> i32 {
    let mut x: i32 = x0;
    zero(&mut x);
    x + 1
}
