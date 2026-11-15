//@ expect: reject
//@ verdict: failed
//@ fn-failed: f::{closure#1}
//@ mechanism: D-103 accounted a clause-free body's `Fn::call` into a local closure that carries a
//@ mechanism: user spec, on the premise that the closure's own verdict answers for its panic
//@ mechanism: paths. A spec-bearing body is not capped by `cap_clause_free_verdict`: its lane
//@ mechanism: trusts every std spec that states no panic precondition, so the closure's verdict
//@ mechanism: does NOT answer for a std call like `Vec::with_capacity`, and the credit imported
//@ mechanism: that weaker standard into the clause-free `verified` of the caller. This is the
//@ mechanism: contract-free soundness twin (closure_contract_free_unchecked_std_call_unaccounted)
//@ mechanism: with `#[ensures(true)]` on the closure and nothing else changed. The fn spelling of
//@ mechanism: the same credit is local_spec_callee_unchecked_std_call_credited.
//@ accept-means: a clause-free body whose only panic path runs through a spec-bearing closure is
//@ accept-means: reported `verified`, and the run exits 0, while the closure's own lane never
//@ accept-means: examined the std call that panics.
//@ fixed-by: D-104 — a call into a spec-bearing local body is accounted only when that body, and
//@ fixed-by: every spec-bearing body it enters in turn, has no unchecked panic site of its own.
//@ fixed-by: D-121 — `with_capacity`'s std spec owes the capacity bound, so the callee's own lane
//@ fixed-by: FAILS on the `n` its contract admits, and no credit rests on the silent spec.
//@ WHY THE CONTRACT IS FALSE: `f` claims (as every clause-free `verified` does) that no execution
//@ WHY THE CONTRACT IS FALSE: panics. `Vec::<u64>::with_capacity(usize::MAX)` needs more than
//@ WHY THE CONTRACT IS FALSE: `isize::MAX` bytes and panics with "capacity overflow" in every build
//@ WHY THE CONTRACT IS FALSE: profile, on the only call `f` makes. The closure's own contract is
//@ WHY THE CONTRACT IS FALSE: false too: it admits every `n`, and `with_capacity(n)` panics for
//@ WHY THE CONTRACT IS FALSE: every `n@ * 8 > isize::MAX@`.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f::{closure#1} verified ✓`, `f verified ✓`, with D-103
//@ teeth: alone; with D-104 `f unknown (partial: panic paths unchecked (call to std::ops::Fn::call
//@ teeth: (unchecked panic paths in f::{closure#1})))`, exit 2, and the closure still `verified`;
//@ teeth: with D-121 `f::{closure#1} FAILED` on `(n@ * 8) <= isize::MAX@`, `f` unchanged.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let c = #[ensures(true)]
    |n: usize| -> usize { Vec::<u64>::with_capacity(n).capacity() };
    let _r = c(usize::MAX);
}
