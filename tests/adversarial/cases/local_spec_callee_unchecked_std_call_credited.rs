//@ expect: reject
//@ verdict: failed
//@ fn-failed: g
//@ mechanism: `unchecked_panic_sites` accounted a clause-free body's call to a local callee that
//@ mechanism: carries a user spec ("its body is its own verification target"). A spec-bearing
//@ mechanism: body is not capped by `cap_clause_free_verdict`: its lane trusts every std spec that
//@ mechanism: states no panic precondition, so the callee's `verified` does not answer for a std
//@ mechanism: call like `Vec::with_capacity`, and the account imported that weaker standard into
//@ mechanism: the caller's clause-free `verified`. `g` carries a `requires` only so that `f` is a
//@ mechanism: verification target (D-71); without it `f` is examined by nobody. D-103 extended the
//@ mechanism: same account to local closures (closure_spec_call_unchecked_std_call_credited).
//@ accept-means: a clause-free body whose only panic path runs through a spec-bearing local fn is
//@ accept-means: reported `verified`, and the run exits 0, while no lane examined the std call
//@ accept-means: that panics.
//@ fixed-by: D-104 — a call into a spec-bearing local body is accounted only when that body, and
//@ fixed-by: every spec-bearing body it enters in turn, has no unchecked panic site of its own. It
//@ fixed-by: predates D-103.
//@ fixed-by: D-121 — `with_capacity`'s std spec owes the capacity bound, so the callee's own lane
//@ fixed-by: FAILS on the `n` its contract admits, and no credit rests on the silent spec.
//@ WHY THE CONTRACT IS FALSE: `f` claims (as every clause-free `verified` does) that no execution
//@ WHY THE CONTRACT IS FALSE: panics. `Vec::<u64>::with_capacity(usize::MAX)` needs more than
//@ WHY THE CONTRACT IS FALSE: `isize::MAX` bytes and panics with "capacity overflow" in every build
//@ WHY THE CONTRACT IS FALSE: profile, on the only call `f` makes. `g`'s own contract is false too:
//@ WHY THE CONTRACT IS FALSE: `n@ >= 0` admits every `n`.
//@ teeth: MEASURED as ACCEPTED, exit 0, `g verified ✓`, `f verified ✓`, with D-103 and before
//@ teeth: D-104; with D-104 `f unknown (partial: panic paths unchecked (call to g (unchecked panic
//@ teeth: paths in g)))`, exit 2, `g` still `verified`; with D-121 `g FAILED` on
//@ teeth: `(n@ * 8) <= isize::MAX@`, `f` unchanged.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(n@ >= 0)]
#[ensures(true)]
pub fn g(n: usize) -> usize {
    Vec::<u64>::with_capacity(n).capacity()
}

pub fn f() {
    let _r = g(usize::MAX);
}
