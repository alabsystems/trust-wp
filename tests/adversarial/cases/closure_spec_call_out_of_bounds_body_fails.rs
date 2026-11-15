//@ expect: reject
//@ verdict: failed
//@ fn-failed: f::{closure#1}
//@ mechanism: a spec-bearing closure's own lane owes the bounds of its index. `f` does not rest on
//@ mechanism: that verdict: the index is a bounds-check assert, which the clause-free account counts
//@ mechanism: as unchecked in the entered body too (D-104), so `f` is `unknown` and only the closure
//@ mechanism: speaks. The pair with closure_spec_call_in_bounds_accounted_control differs in the
//@ mechanism: index literal alone.
//@ fixed-by: D-103 — the closure's own lane owes the panic path; D-104 — the caller is not credited
//@ fixed-by: for a body with an unchecked site.
//@ accept-means: the closure lane stopped checking its own bounds, and an index panic reachable
//@ accept-means: from `f` is reported nowhere.
//@ WHY THE CONTRACT IS FALSE: the closure indexes `[1, 2, 3]` at 5 and panics on every call,
//@ WHY THE CONTRACT IS FALSE: which its (implicit) no-panic obligation forbids.
//@ teeth: structural, not a knob: rejected with and without D-103 and D-104, by the closure's own
//@ teeth: `FAILED`.
//@ also-verified: f
//@ note: `f` is credited modularly: its call into the closure is accounted because the bounds
//@ note: check inside it is a charged obligation of the closure's own lane, which FAILS here and
//@ note: fails the run. That is the modular credit D-104 states it takes.
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
        let i = 5usize;
        v[i]
    };
    let _r = c();
}
