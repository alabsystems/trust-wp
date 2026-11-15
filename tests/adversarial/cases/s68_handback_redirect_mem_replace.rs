//@ expect: reject
//@ mechanism: sibling of s68_handback_redirect_direct: `t` is redirected by `std::mem::replace(&mut t,
//@ mechanism: &mut y)` (whose result carries a borrow, so THAT call gets no handback). Before 8a909ade the
//@ mechanism: handback at `zero(t)` read `t`'s value off its one write `t = &mut x` and credited `x`.
//@ fixed-by: wp-s68 v2 8a909ade — `t` is the target of `Rvalue::Ref(Mut, t)` (the `&mut t` argument), so
//@ fixed-by: it is refused as a fresh reborrow source; the handback speaks about `*t` instead.
//@ accept-means: `post_x == 0` assumed after `zero(t)` although `t` points at `y`.
//@ WHY THE PROGRAM IS WRONG: `mem::replace` stores `&mut y` into `t`; `zero(t)` zeroes `y`; `x` stays
//@ WHY THE PROGRAM IS WRONG: `i32::MAX` and `x + 1` overflows.
//@ teeth: NOT shown to accept on any build: both sides of the 2026-09-18 A/B (e552908e, 8a909ade) land as
//@ teeth: `probe_mem_replace vacuous (contradictory premises)`, exit 2 — the vacuity guard, not the
//@ teeth: handback, pinned here as the verdict so a change to it is visible. The instrumented A/B showed
//@ teeth: the handback's credit move from `x` (through_deref=false) to `*t` (through_deref=true). The
//@ teeth: parameter-initialised sibling s68_handback_redirect_mem_replace_param has no constant premise
//@ teeth: to contradict and pins the handback as the deciding guard.
//@ verdict: error
//@ refused-with: vacuous (contradictory premises)
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

// Redirect `t` with std::mem::replace (result carries a borrow, so no handback there).
pub fn probe_mem_replace() -> i32 {
    let mut x: i32 = i32::MAX;
    let mut y: i32 = 0;
    let mut t: &mut i32 = &mut x;
    let _ = std::mem::replace(&mut t, &mut y);
    zero(t);
    x + 1
}
