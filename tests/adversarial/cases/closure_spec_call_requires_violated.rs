//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: the obligation half of the credit D-103 grants at a call into a spec-bearing closure:
//@ mechanism: the site is accounted only because the call lane charges that closure's own
//@ mechanism: `requires` there. Were the charge ever dropped while the account stayed, `f` would
//@ mechanism: owe nothing, its only call would be credited, and it would verify.
//@ fixed-by: D-103 — the account and the charge read one resolver and one spec table.
//@ accept-means: a closure's `requires` is no longer owed at a call that the panic account
//@ accept-means: credits, and the closure's body runs outside the precondition it was verified under.
//@ WHY THE CONTRACT IS FALSE: `c(1000)` violates `x@ < 1000`; `f` owes that precondition.
//@ teeth: structural, not a knob: `f FAILED` with D-103 and without it. It pins the obligation the
//@ teeth: account rests on rather than the account itself.
//@ also-verified: f::{closure#0}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let c = #[requires(x@ < 1000)]
    #[ensures(result@ == x@ + 1)]
    |x: usize| x + 1;
    let _y = c(1000);
}
