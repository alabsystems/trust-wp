//@ expect: reject
//@ mechanism: sibling of s68_handback_redirect_direct: a CONDITIONAL redirect of `t` inside an uncontracted
//@ mechanism: helper `pick(&mut t, &mut y, take_other)`. Before 8a909ade the handback read `t`'s value
//@ mechanism: off its one write `t = &mut x` and credited `x` with `zero`'s `^p == 0` on every path.
//@ fixed-by: wp-s68 v2 8a909ade — `t` is the target of `Rvalue::Ref(Mut, t)`, so it is refused as a fresh
//@ fixed-by: reborrow source; the handback speaks about `*t` instead.
//@ accept-means: `post_x == 0` assumed after `zero(t)` on the `take_other` path where `t` points at `y`.
//@ WHY THE PROGRAM IS WRONG: with `take_other == true`, `pick` stores `&mut y` into `t`; `zero(t)` zeroes
//@ WHY THE PROGRAM IS WRONG: `y`; `x` stays `i32::MAX` and `x + 1` overflows.
//@ teeth: NOT shown to accept on any build: both sides of the 2026-09-18 A/B (e552908e, 8a909ade) are
//@ teeth: refused by the encoder's final-collapse constant-carrier arm (`^Int(2147483647)`), an
//@ teeth: unrelated guard; the driver counts that encoding refusal as `errors=1`,
//@ teeth: which the runner reads as `unknown`, and `refused-with:` pins its text. The instrumented A/B showed the handback's credit
//@ teeth: move from `x` (through_deref=false) to `*t` (through_deref=true); see
//@ teeth: s68_handback_redirect_call and s68_handback_redirect_mem_replace_param.
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

fn pick<'a>(slot: &mut &'a mut i32, other: &'a mut i32, take_other: bool) {
    if take_other {
        *slot = other;
    }
}

// Conditional redirection through a helper; x stays MAX when take_other is true.
pub fn probe_pick(take_other: bool) -> i32 {
    let mut x: i32 = i32::MAX;
    let mut y: i32 = 0;
    let mut t: &mut i32 = &mut x;
    pick(&mut t, &mut y, take_other);
    zero(t);
    x + 1
}
