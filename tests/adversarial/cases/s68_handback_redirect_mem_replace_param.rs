//@ expect: reject
//@ mechanism: s68_handback_redirect_mem_replace with `x`/`y` initialised from parameters, so no constant
//@ mechanism: premise exists for the vacuity or final-collapse guards to trip on: the reborrow handback at
//@ mechanism: `zero(t)` is the deciding guard. Before 8a909ade it read `t`'s value off its one write
//@ mechanism: `t = &mut x` and credited `x` with `^p == 0` although `mem::replace` had redirected `t` to `y`.
//@ fixed-by: wp-s68 v2 8a909ade — `t` is the target of `Rvalue::Ref(Mut, t)`, so it is refused as a fresh
//@ fixed-by: reborrow source; the handback speaks about `*t` instead, which the walk cannot relate to `x`.
//@ accept-means: `post_x == 0` assumed after `zero(t)`: `x + 1` proved in range for a program that
//@ accept-means: overflows at `x0 == i32::MAX`.
//@ WHY THE PROGRAM IS WRONG: `mem::replace` stores `&mut y` into `t`; `zero(t)` zeroes `y`; `x` keeps
//@ WHY THE PROGRAM IS WRONG: `x0`; with `x0 == i32::MAX`, `x + 1` overflows.
//@ teeth: A/B'd 2026-09-18 in one workspace. At e552908e (fix absent) the overflow obligation was
//@ teeth: DISCHARGED: `ay_result=unsat`, and only the unrelated partial marker `unknown (partial: panic
//@ teeth: paths unchecked (call to std::mem::replace))` kept the run from a clean accept — the
//@ teeth: instrumented driver printed `param p <- caller local x through_deref=false`. At 8a909ade the
//@ teeth: same obligation is REFUTED: `probe_mem_replace_param FAILED ✗ (postcondition)`,
//@ teeth: `ay_result=sat`, model validated.
//@ verdict: failed
//@ fn-failed: probe_mem_replace_param
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

pub fn probe_mem_replace_param(x0: i32, y0: i32) -> i32 {
    let mut x: i32 = x0;
    let mut y: i32 = y0;
    let mut t: &mut i32 = &mut x;
    let _ = std::mem::replace(&mut t, &mut y);
    zero(t);
    x + 1
}
