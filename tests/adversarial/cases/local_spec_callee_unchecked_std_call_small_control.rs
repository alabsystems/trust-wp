//@ expect: verify
//@ xfail: D-104's price. `g`'s body calls `Vec::with_capacity`, a std call, which the clause-free
//@ xfail: account counts as an unchecked site in every body it enters, so the call into `g` is
//@ xfail: unaccounted whatever the capacity: `f unknown (partial: panic paths unchecked (call to g
//@ xfail: (unchecked panic paths in g)))`. `g`'s own lane owes the capacity bound (D-121) and
//@ xfail: verifies. Retiring this needs the account to credit a std call whose spec owes all its
//@ xfail: panics, not a wider credit at the call.
//@ mechanism: the TRUE twin of local_spec_callee_unchecked_std_call_credited: `g` bounds the
//@ mechanism: capacity its contract admits, so `g`'s contract is true, and `f` asks for a capacity
//@ mechanism: within that bound. An XPASS here while the RED twin still rejects is the signal that
//@ mechanism: the call into `g` became accountable.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `verified` before D-104, where the twin was ACCEPTED too; `unknown`, the same
//@ teeth: verdict as its twin, with D-104. D-121 made the twin's `g` false on its own lane, so
//@ teeth: `g` here bounds `n`: `g verified ✓`, `f` still `unknown`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ <= 1024)]
#[ensures(true)]
pub fn g(n: usize) -> usize {
    Vec::<u64>::with_capacity(n).capacity()
}

pub fn f() {
    let _r = g(8);
}
