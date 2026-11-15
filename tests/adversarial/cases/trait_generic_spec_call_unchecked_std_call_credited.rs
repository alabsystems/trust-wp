//@ expect: reject
//@ verdict: failed
//@ fn-failed: <S as Tr>::m
//@ mechanism: the generic spelling of trait_impl_spec_call_unchecked_std_call_credited. Inside the
//@ mechanism: generic `f` the call `t.m(..)` has no body to enter: the instance does not resolve,
//@ mechanism: and ANY impl a caller supplies — here `S`'s, which calls a std function whose spec
//@ mechanism: states no panic precondition — is verified at the contract-bearing standard only.
//@ accept-means: a generic call through a contracted trait method credits every impl unseen.
//@ fixed-by: D-104 — a call whose entered body is not determined is not accounted.
//@ fixed-by: D-121 — `with_capacity`'s std spec owes the capacity bound, so the callee's own lane
//@ fixed-by: FAILS on the `n` its contract admits, and no credit rests on the silent spec.
//@ WHY THE CONTRACT IS FALSE: `f`'s clause-free `verified` claims no execution panics for every
//@ WHY THE CONTRACT IS FALSE: `T: Tr`; `h` instantiates it at `S`, whose `m` runs
//@ WHY THE CONTRACT IS FALSE: `Vec::<u64>::with_capacity(usize::MAX)` and panics with "capacity
//@ WHY THE CONTRACT IS FALSE: overflow".
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, before D-104; `f unknown (partial: panic
//@ teeth: paths unchecked (call to Tr::m))` with it, `<S as Tr>::m` still `verified`; with D-121
//@ teeth: `<S as Tr>::m FAILED` on `(n@ * 8) <= isize::MAX@`, `f` unchanged.
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

pub fn f<T: Tr>(t: &T) {
    let _r = t.m(usize::MAX);
}

pub fn h() {
    f(&S);
}
