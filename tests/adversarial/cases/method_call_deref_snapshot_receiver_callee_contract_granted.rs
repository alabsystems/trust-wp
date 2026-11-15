//@ expect: reject
//@ also-verified: g
//@ mechanism: method_call_deref_snapshot_receiver_read_at_snapshot_type_granted.rs read at a CALL SITE.
//@ mechanism: `g`'s contract `result == (*s).m()` is `A`'s inherent `m` (false), and `g` returns
//@ mechanism: false. A caller reads `g`'s contract as text; the callee-text resolver types the receiver
//@ mechanism: `(*s)` at `s`'s own type `Snapshot<A>` (`identity_typed::prefixed_receiver_type` reads
//@ mechanism: through a reference or a box only) and reads `<Snapshot<A> as Tr>::m` (true): `caller`,
//@ mechanism: which returns `g(..)` (false), is credited with `result == true`.
//@ fixed-by: D-201 — REFUSED: a `*x` receiver of an `x` that is neither a reference nor a box is
//@ fixed-by: untyped, and the owner resolver refuses a family call on it (`Resolver::is_opaque_deref`)
//@ fixed-by: as the callee-text resolver does (`identity_typed::prefixed_receiver_type`).
//@ accept-means: `caller` claims `result == true` and returns false; ACCEPTED means that credit is
//@ accept-means: printed.
//@ teeth: MEASURED: `caller verified ✓` (and `g FAILED`) with D-200 in force.
//@ teeth: With D-201: REFUSED (`unknown`): `g` and `caller` error on the unresolved marker.
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
pub fn g(s: Snapshot<A>) -> bool {
    let _ = s;
    false
}

#[ensures(result == true)]
pub fn caller() -> bool {
    g(snapshot!(A))
}
