//@ expect: reject
//@ mechanism: `f(s: S, k: fn(S) -> Int)` claims `result@ == k(s)`. The bare `k` is the parameter:
//@ mechanism: a value binding of the clause's own scope, which Rust (and Creusot, which refuses a
//@ mechanism: program function called in a specification) reads before any item, so the claim is
//@ mechanism: about an arbitrary function and cannot be proved. The crate's only logic `k` is the
//@ mechanism: method `Tr::k`, whose impl for `S` is 10. The resolver skips a call whose name a
//@ mechanism: binder or parameter binds, and leaves it under its written name; the encoder then
//@ mechanism: dispatches the colliding method name on its first argument's sort and reads
//@ mechanism: `<S as Tr>::k(s)` (10), so `f`, which returns 10, is credited.
//@ fixed-by: D-199 — REFUSED: a call whose name a parameter or binder binds is that binding, and
//@ fixed-by: the resolver spells it with the refusal marker (`Resolver::resolve_call_name_unchecked`)
//@ fixed-by: instead of leaving it for the encoder's receiver dispatch.
//@ accept-means: `f` claims `result@ == k(s)` with Rust's `k` the parameter, returns 10, and the crate
//@ accept-means: exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-198 in force.
//@ teeth: With D-199: REFUSED (`unknown`): `f` errors on the unresolved marker `__lfidU__k`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn k(self) -> Int;
}

pub struct S;
impl Tr for S {
    #[logic(open)]
    fn k(self) -> Int {
        pearlite! { 10 }
    }
}

#[ensures(result@ == k(s))]
pub fn f(s: S, k: fn(S) -> Int) -> u32 {
    10
}
