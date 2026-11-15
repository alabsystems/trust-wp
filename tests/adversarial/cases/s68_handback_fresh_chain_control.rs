//@ expect: verify
//@ mechanism: control for the s68_handback_redirect_* rejects, on the exact code path 8a909ade tightened:
//@ mechanism: `let t = &mut x; zero(t)` is MIR `_t = &mut x; _k = &mut (*_t); zero(move _k)`, a reborrow
//@ mechanism: chain through `t`. `t` is never borrowed (the `&mut *t` reborrow lends its POINTEE and is
//@ mechanism: not an escape of `t`), never captured, written once — so its value at the call IS `&mut x`
//@ mechanism: and the handback may credit `x` with `^p == 0`.
//@ fixed-by: n/a — over-refusal guard for wp-s68 v2 8a909ade (the `inc_max_3` shape in miniature).
//@ teeth: control - must keep verifying. Verified on both sides of the 2026-09-18 A/B (e552908e and
//@ teeth: 8a909ade); the instrumented driver printed
//@ teeth: `param p <- caller local x through_deref=false` on both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^p == 0)]
fn zero(p: &mut i32) {
    *p = 0;
}

pub fn probe_control() -> i32 {
    let mut x: i32 = i32::MAX;
    let t: &mut i32 = &mut x;
    zero(t);
    x + 1
}
