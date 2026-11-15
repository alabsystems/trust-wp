//@ expect: verify
//@ xfail: `die()` is now a verification target of its own, and its only goal is Creusot's
//@ xfail: `Terminator::Abort` — "this body is unreachable" — which is genuinely refutable
//@ xfail: for a body that always panics (D-27; see i3_body_panic_unconditional). The
//@ xfail: caller's claim, which is what this case is about, still verifies. Reaching an
//@ xfail: XPASS would take a `#[requires(false)]` on the callee, not a weaker verdict.
//@ mechanism: a contract-free panicking -> ! callee made unreachable by the caller precondition
//@ accept-means: n/a (control) — TRUE contract, must keep verifying
//@ fixed-by: wp-s40 diverging-callees
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn die() -> ! { panic!() }
#[requires(x@ > 0)]
#[ensures(true)]
pub fn f(x: i32) { if x <= 0 { die() } }
