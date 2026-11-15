//@ expect: reject
//@ mechanism: sibling of s68_handback_redirect_direct: the redirect of `t` happens inside an uncontracted
//@ mechanism: helper `redirect(&mut t, &mut y)`. Before 8a909ade the handback read `t`'s value off its
//@ mechanism: one write `t = &mut x` (the `&mut t` argument is not a write naming `t`) and credited `x`
//@ mechanism: with `zero`'s `^p == 0`.
//@ fixed-by: wp-s68 v2 8a909ade — `t` is the target of `Rvalue::Ref(Mut, t)` (the `&mut t` argument), so
//@ fixed-by: it is refused as a fresh reborrow source; the handback speaks about `*t` instead.
//@ accept-means: `post_x == 0` assumed after `zero(t)` although `t` points at `y`: `x + 1` proved in range
//@ accept-means: for a program that overflows.
//@ WHY THE PROGRAM IS WRONG: `redirect` stores `&mut y` into `t`; `zero(t)` zeroes `y`; `x` stays
//@ WHY THE PROGRAM IS WRONG: `i32::MAX` and `x + 1` overflows.
//@ teeth: NOT shown to accept on any build: on both sides of the 2026-09-18 A/B (e552908e and 8a909ade)
//@ teeth: the run is refused by the encoder's final-collapse constant-carrier arm (`^Int(2147483647)`),
//@ teeth: which fires with or without `zero`'s contract (p1e_redirect_nocontract) — an UNRELATED guard.
//@ teeth: The driver counts that encoding refusal as `errors=1`, which the runner reads as `unknown`;
//@ teeth: `refused-with:` pins its text so a change to it is visible. What the A/B did show, with an
//@ teeth: instrumented driver printing every granted handback: before, `param p <- caller local x
//@ teeth: through_deref=false` (the wrong credit, masked by the collapse refusal); after, `param p <-
//@ teeth: caller local t through_deref=true`. The handback refuses this shape on its own now; the
//@ teeth: sibling s68_handback_redirect_mem_replace_param pins the same refusal where it is the
//@ teeth: deciding guard (`FAILED` vs a falsely discharged obligation).
//@ verdict: unknown
//@ refused-with: final-collapse refused
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

// x stays i32::MAX (zero() writes y through the redirected t), so `x + 1` overflows.
pub fn probe_redirect_call() -> i32 {
    let mut x: i32 = i32::MAX;
    let mut y: i32 = 0;
    let mut t: &mut i32 = &mut x;
    redirect(&mut t, &mut y);
    zero(t);
    x + 1
}
