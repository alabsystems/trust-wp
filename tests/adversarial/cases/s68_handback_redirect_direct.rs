//@ expect: reject
//@ mechanism: reborrow_handback (cbf071ec) read `t`'s value at `zero(t)` off its ONE whole-local write
//@ mechanism: `t = &mut x` and handed the callee's `^p` to `x` — although `t` is itself mutably borrowed
//@ mechanism: (`tt = &mut t`) and reassigned THROUGH that borrow (`*tt = &mut y`), so at the call `t`
//@ mechanism: points at `y`. The fact granted (about `x`) and the fact owed (about `*t` at the call) came
//@ mechanism: from different premises: the campaign's signature defect.
//@ fixed-by: wp-s68 v2 8a909ade — `single_mut_borrow_definition` refuses a local that escapes by reference
//@ fixed-by: (any borrow / raw pointer of the local itself, closure capture by value, asm/yield output);
//@ fixed-by: the handback falls back to `*t` (the pointee of whatever `t` holds), never tracks the redirect.
//@ accept-means: `post_x == 0` was assumed on the path after `zero(t)` while the program left `x` at
//@ accept-means: `i32::MAX`; `x + 1` was proved in range. Compiled with overflow checks the program panics.
//@ WHY THE PROGRAM IS WRONG: `*tt = &mut y` redirects `t` to `y`; `zero(t)` zeroes `y`; `x` stays
//@ WHY THE PROGRAM IS WRONG: `i32::MAX`, so `x + 1` overflows (the reviewer ran it: it panics).
//@ teeth: A/B'd in one workspace: at wp-s68 e552908e (cbf071ec present, fix absent)
//@ teeth: `probe_redirect_direct verified ✓`, base_exit_code=0 — the confirmed FALSE ACCEPT that
//@ teeth: rejected s68 v1 (review probe p1b_redirect_direct). At 8a909ade
//@ teeth: `probe_redirect_direct FAILED ✗ (postcondition)` with a counterexample. An instrumented driver
//@ teeth: printed the granted handback on both sides: before `param p <- caller local x
//@ teeth: through_deref=false`, after `param p <- caller local t through_deref=true`, i.e. the credit
//@ teeth: now speaks about `*t`, which the walk cannot relate to `x` (dbgpre/dbgfix logs beside the probe).
//@ verdict: failed
//@ fn-failed: probe_redirect_direct
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

// The redirection is a plain projected write through a `&mut &mut i32`, no call.
pub fn probe_redirect_direct() -> i32 {
    let mut x: i32 = i32::MAX;
    let mut y: i32 = 0;
    let mut t: &mut i32 = &mut x;
    let tt: &mut &mut i32 = &mut t;
    *tt = &mut y;
    zero(t);
    x + 1
}
