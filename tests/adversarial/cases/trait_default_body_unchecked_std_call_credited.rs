//@ expect: reject
//@ verdict: failed
//@ fn-failed: Tr::m
//@ mechanism: the default-body spelling of trait_impl_spec_call_unchecked_std_call_credited. `S`
//@ mechanism: overrides nothing, so `S.m(..)` resolves to the trait's own default body, which
//@ mechanism: calls a std function whose spec states no panic precondition.
//@ accept-means: a call that runs a contracted default body is credited on its contract alone.
//@ fixed-by: D-104 — the default body is the entered body, held to the clean-body rule.
//@ fixed-by: D-121 — `with_capacity`'s std spec owes the capacity bound, so the callee's own lane
//@ fixed-by: FAILS on the `n` its contract admits, and no credit rests on the silent spec.
//@ WHY THE CONTRACT IS FALSE: `f` claims (as every clause-free `verified` does) that no execution
//@ WHY THE CONTRACT IS FALSE: panics; the default `m` runs `Vec::<u64>::with_capacity(usize::MAX)`,
//@ WHY THE CONTRACT IS FALSE: which panics with "capacity overflow". The default body's own
//@ WHY THE CONTRACT IS FALSE: contract is false too: it admits every `n`.
//@ teeth: MEASURED as ACCEPTED, exit 0, `Tr::m verified ✓`, `f verified ✓`, before D-104; `f
//@ teeth: unknown (partial: panic paths unchecked (call to Tr::m (unchecked panic paths in
//@ teeth: Tr::m)))` with it, `Tr::m` still `verified`; with D-121 `Tr::m FAILED` on
//@ teeth: `(n@ * 8) <= isize::MAX@`, `f` unchanged.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[requires(n@ >= 0)]
    #[ensures(true)]
    fn m(&self, n: usize) -> usize {
        Vec::<u64>::with_capacity(n).capacity()
    }
}

pub struct S;

impl Tr for S {}

pub fn f() {
    let _r = S.m(usize::MAX);
}
