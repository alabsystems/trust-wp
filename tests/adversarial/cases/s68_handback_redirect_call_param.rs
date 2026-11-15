//@ expect: reject
//@ mechanism: s68_handback_redirect_call with `x`/`y` initialised from parameters (no constant carrier for
//@ mechanism: the final-collapse arm). Before 8a909ade the handback credited `x` with `zero`'s `^p == 0`
//@ mechanism: although the uncontracted `redirect(&mut t, &mut y)` had redirected `t` to `y`.
//@ fixed-by: wp-s68 v2 8a909ade — `t` is the target of `Rvalue::Ref(Mut, t)`, so it is refused as a fresh
//@ fixed-by: reborrow source; the handback speaks about `*t` instead.
//@ accept-means: `post_x == 0` assumed after `zero(t)`: `x + 1` proved in range for a program that
//@ accept-means: overflows at `x0 == i32::MAX`.
//@ WHY THE PROGRAM IS WRONG: `redirect` stores `&mut y` into `t`; `zero(t)` zeroes `y`; `x` keeps `x0`.
//@ teeth: NOT shown to accept on any build: both sides of the 2026-09-18 A/B (e552908e, 8a909ade) report
//@ teeth: `unknown (refutation withheld: solver evidence was trust-wp-structural-provenance, not a
//@ teeth: satisfying counterexample model)`, `assertions=6` — a refutation that does not depend on the
//@ teeth: handback (the instrumented driver still printed the wrong `x` credit before the fix). Pinned
//@ teeth: so the shape stays covered; s68_handback_redirect_mem_replace_param is the sibling whose
//@ teeth: verdict the handback decides.
//@ verdict: unknown
//@ also-verified: zero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^p == 0)]
fn zero(p: &mut i32) {
    *p = 0;
}

fn redirect<'a>(t: &mut &'a mut i32, y: &'a mut i32) {
    *t = y;
}

pub fn probe_redirect_call_param(x0: i32, y0: i32) -> i32 {
    let mut x: i32 = x0;
    let mut y: i32 = y0;
    let mut t: &mut i32 = &mut x;
    redirect(&mut t, &mut y);
    zero(t);
    x + 1
}
