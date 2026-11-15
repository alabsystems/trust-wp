//@ expect: verify
//@ xfail: D-104's price. The closure's body calls `Vec::with_capacity`, a std call, which the
//@ xfail: clause-free account counts as an unchecked site in every body it enters, so the call
//@ xfail: into the closure is unaccounted whatever the capacity: `f unknown (partial: panic
//@ xfail: paths unchecked (call to std::ops::Fn::call (unchecked panic paths in
//@ xfail: f::{closure#0})))`. The closure's own lane owes the capacity bound (D-121) and
//@ xfail: verifies. Retiring this needs the account to credit a std call whose spec owes all its
//@ xfail: panics, not a wider credit at the call.
//@ mechanism: the TRUE twin of closure_spec_call_unchecked_std_call_credited: the closure bounds the
//@ mechanism: capacity its contract admits, so its contract is true, and `f` asks for a capacity
//@ mechanism: within that bound. It pins the over-refusal side of what closed that case: an XPASS
//@ mechanism: here while the RED twin still rejects is the signal that the call into the closure
//@ mechanism: became accountable.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `verified` with D-103 alone, where the twin was ACCEPTED too; `unknown`, the
//@ teeth: same verdict as its twin, with D-104. D-121 made the twin's closure false on its own
//@ teeth: lane, so the closure here bounds `n`: `f::{closure#0} verified ✓`, `f` still `unknown`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let c = #[requires(n@ <= 1024)]
    #[ensures(true)]
    |n: usize| -> usize { Vec::<u64>::with_capacity(n).capacity() };
    let _r = c(8);
}
