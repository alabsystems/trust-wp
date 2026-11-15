//@ expect: reject
//@ also-verified: g
//@ mechanism: a callee's `requires` over a `&mut` a destructuring parameter binds is stated over the
//@ mechanism: parameter's projection (D-179), `*(__twp_arg0.0) < 100`, and a call owes it over the
//@ mechanism: argument it passes: `*x < 100` for `g((x, y))`. Accepted, the call was granted the
//@ mechanism: callee without owing its precondition.
//@ accept-means: a caller was credited without establishing the precondition its callee states over a
//@ accept-means: destructured `&mut`.
//@ WHY THE CONTRACT IS FALSE: with `*x == 200`, `caller` calls `g` outside its precondition, and `g`'s
//@ WHY THE CONTRACT IS FALSE: `*p += 1` is then owed nothing it can rely on; `caller` states no
//@ WHY THE CONTRACT IS FALSE: `requires` that rules the call out.
//@ fixed-by: n/a — the obligation side of destructured_mut_ref_requires_discharged_at_call_control:
//@ fixed-by: the projection the callee is proved under is the one each call owes.
//@ teeth: the isolating twin with `#[requires(*x < 50 && *x > -50)]` on `caller` is
//@ teeth: destructured_mut_ref_requires_discharged_at_call_control, which verifies; this case is
//@ teeth: rejected (`caller unknown`) with `g verified`, so the call reads `g`'s `requires`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*p < 100i32 && *p > -100i32)]
pub fn g((p, _q): (&mut i32, &mut i32)) {
    *p += 1;
}

#[ensures(true)]
pub fn caller(x: &mut i32, y: &mut i32) {
    g((x, y));
}
