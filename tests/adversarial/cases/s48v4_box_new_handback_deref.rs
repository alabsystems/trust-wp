//@ expect: reject
//@ mechanism: the `std::boxed::Box::new` entry of the ExternSpec borrow-forwarding allowlist — v3 kept it on the argument that the `&mut` is MOVED into the box, but moving a `&mut` into a container does not end the reborrow: `*b` hands it straight back and the caller writes through it.
//@ fixed-by: wp-s48 v4 (criterion corrected to "no live `&mut` reborrow of the argument is REACHABLE FROM THE RESULT"; `Box::new`, `Rc::new` and `Arc::new` deleted)
//@ accept-means: `Box::new(&mut x)` freezes `x` at its entry value for the rest of the function, so a write through the `&mut i32` moved back out of the box is invisible to every later read of `x`.
//@ WHY THE PROGRAM IS WRONG: `*r = 7` writes through the borrow of `x` that the box handed back, so `x` is 7 at the proof_assert; the assertion claims 5.
//@ teeth: A/B'd 2026-09-14 on this branch: re-adding ONLY `"std::boxed::Box::new"` to
//@ teeth: FORWARDING_STD_CALLEES and rebuilding turns this case ACCEPTED (exit 0,
//@ teeth: `proof_assert ... verified ✓`); with the audited list it is `unknown`
//@ teeth: (exit 2, fail-closed). It also accepted at wp-s48 b30c81b5 and on
//@ teeth: wp-campaign (on a probe that moved the borrow into a box and read it back out, and the
//@ teeth: s48 v4 review's own rv3 reproduction), so the hole predates this front.
//@ verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn k() {
    let mut x = 5i32;
    let b = Box::new(&mut x);
    let r: &mut i32 = *b;
    *r = 7;
    proof_assert!(x == 5i32);
}
