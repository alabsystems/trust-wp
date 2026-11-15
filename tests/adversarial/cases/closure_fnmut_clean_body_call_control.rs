//@ expect: verify
//@ xfail: D-104's price. `f`'s two calls go through `FnMut::call_mut`, which enters no body for the
//@ xfail: clause-free account, so `f` is `unknown (partial: panic paths unchecked (call to
//@ xfail: std::ops::FnMut::call_mut))` although the closure's body has no panic site at all.
//@ xfail: Retiring it needs the capture invariants an `FnMut` body is granted to be owed at every
//@ xfail: entry (D-77 closed), not a wider credit at the call.
//@ mechanism: the control for closure_fnmut_reentry_capture_invariant_credited: a spec-bearing
//@ mechanism: `FnMut` closure called twice whose body is clean and whose capture has no invariant.
//@ mechanism: An XPASS here while its RED twin still rejects is the signal that re-entry premises
//@ mechanism: became owed.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified ✓` with the knob that let `FnMut::call_mut` through the clean-body
//@ teeth: rule, `f unknown (partial: ...)` without it, on the same binary.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let mut k = 0u32;
    let mut c = #[ensures(true)]
    || {
        k = 1;
    };
    c();
    c();
}
