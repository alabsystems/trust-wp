//@ expect: reject
//@ mechanism: `(*s).m()` with `s: Snapshot<A>`: `*s` is the snapshot's `A`, where Rust's method lookup
//@ mechanism: starts and takes `A`'s inherent `m` (false). The crate also implements a local trait
//@ mechanism: `Tr` for `Snapshot<A>` whose `m` is true. The resolver types a `*x` receiver at `x`'s own
//@ mechanism: type unless `x` is a reference or a box, so it resolves the call at `Snapshot<A>` and
//@ mechanism: reads `<Snapshot<A> as Tr>::m` (true): `f`, which returns true, is credited.
//@ fixed-by: D-201 — REFUSED: a `*x` receiver of an `x` that is neither a reference nor a box is
//@ fixed-by: untyped, and the owner resolver refuses a family call on it (`Resolver::is_opaque_deref`)
//@ fixed-by: as the callee-text resolver does (`identity_typed::prefixed_receiver_type`).
//@ accept-means: `f` claims `result == A::m(*s)` (false), returns true, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-200 in force.
//@ teeth: With D-201: REFUSED (`unknown`): `f` errors on the unresolved marker `__lfidU__m`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct A;
impl A {
    #[logic(open)]
    pub fn m(self) -> bool {
        pearlite! { false }
    }
}

pub trait Tr {
    #[logic]
    fn m(self) -> bool;
}

impl Tr for Snapshot<A> {
    #[logic(open)]
    fn m(self) -> bool {
        pearlite! { true }
    }
}

#[ensures(result == (*s).m())]
pub fn f(s: Snapshot<A>) -> bool {
    let _ = s;
    true
}
