//@ expect: verify
//@ xfail: D-104's price. The closure's index is a MIR bounds-check assert, which
//@ xfail: `unchecked_panic_sites` counts as unchecked in every body it reads, so the closure's
//@ xfail: body is not clean and `f` stays `unknown (partial: panic paths unchecked (call to
//@ xfail: std::ops::Fn::call (unchecked panic paths in f::{closure#1})))` — although this closure's
//@ xfail: own lane does owe the bounds check (its twin reports `f::{closure#1} FAILED`). Retiring it
//@ xfail: needs the account to credit the bounds obligation where a lane owes it, in the entered
//@ xfail: body and the caller's own body alike.
//@ mechanism: the TRUE twin of closure_spec_call_out_of_bounds_body_fails, identical but for the
//@ mechanism: index literal. A clause-free `f` calls, through `Fn::call`, a closure that carries a
//@ mechanism: user spec and whose lane checks the bounds of its index.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified ✓` with D-103 alone; `f unknown (partial: ...)` with D-104 and
//@ teeth: without D-103. Its twin with index 5 reports `f::{closure#1} FAILED` on all three.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(unconditional_panic)]

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let c = #[ensures(true)]
    || -> u32 {
        let v = [1u32, 2, 3];
        let i = 2usize;
        v[i]
    };
    let _r = c();
}
