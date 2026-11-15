//@ expect: reject
//@ verdict: failed
//@ fn-failed: <S as Tr>::m
//@ mechanism: the trait arm of the clause-free account. `S.m(..)` names the trait method `Tr::m`,
//@ mechanism: whose contract the call lane charges, and the account credited the site on that
//@ mechanism: contract alone — never asking which body runs. The instance resolves to `S`'s impl,
//@ mechanism: whose body calls a std function whose spec states no panic precondition.
//@ accept-means: a call through a contracted trait method credits whatever body the impl has.
//@ fixed-by: D-104 — the site enters the body its instance resolves to, and is accounted only
//@ fixed-by: when that body is clean.
//@ fixed-by: D-121 — `with_capacity`'s std spec owes the capacity bound, so the callee's own lane
//@ fixed-by: FAILS on the `n` its contract admits, and no credit rests on the silent spec.
//@ WHY THE CONTRACT IS FALSE: `f` claims (as every clause-free `verified` does) that no execution
//@ WHY THE CONTRACT IS FALSE: panics; `S`'s `m` runs `Vec::<u64>::with_capacity(usize::MAX)`, which
//@ WHY THE CONTRACT IS FALSE: panics with "capacity overflow". The impl's own contract is false
//@ WHY THE CONTRACT IS FALSE: too: it admits every `n`.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, before D-104; `f unknown (partial: panic
//@ teeth: paths unchecked (call to Tr::m (unchecked panic paths in <S as Tr>::m)))` with it, the
//@ teeth: impl still `verified`; with D-121 `<S as Tr>::m FAILED` on `(n@ * 8) <= isize::MAX@`, `f`
//@ teeth: unchanged.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[requires(n@ >= 0)]
    #[ensures(true)]
    fn m(&self, n: usize) -> usize;
}

pub struct S;

impl Tr for S {
    #[requires(n@ >= 0)]
    #[ensures(true)]
    fn m(&self, n: usize) -> usize {
        Vec::<u64>::with_capacity(n).capacity()
    }
}

pub fn f() {
    let _r = S.m(usize::MAX);
}
