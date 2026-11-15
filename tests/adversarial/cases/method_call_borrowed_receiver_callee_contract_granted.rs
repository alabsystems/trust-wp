//@ expect: reject
//@ also-verified: g
//@ mechanism: method_call_borrowed_receiver_read_at_pointee_type_granted.rs read at a CALL SITE. `g`'s
//@ mechanism: contract `result == (&a).invariant()` is `<&A as Invariant>::invariant` (true) and `g`
//@ mechanism: returns true. A caller reads `g`'s contract as text, whose receiver `(&a)` the callee-text
//@ mechanism: resolver strips to the parameter `a` and types `A`
//@ mechanism: (`identity_typed::prefixed_paren_receiver`), reading the inherent `A::invariant`
//@ mechanism: (false): `caller`, which returns `g(a)` (true), is credited with `result == false`.
//@ fixed-by: D-201 — REFUSED: the contract parser spells a method call whose receiver has a
//@ fixed-by: reference level it drops with the refusal marker (`resolve_method_call`), whatever
//@ fixed-by: the call names.
//@ accept-means: `caller` claims `result == false` and returns true; ACCEPTED means that credit is
//@ accept-means: printed.
//@ teeth: MEASURED: `caller verified ✓` with D-199 in force.
//@ teeth: With D-201: REFUSED (`unknown`): `g` and `caller` error on the unresolved marker.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct A;
impl A {
    #[logic(open)]
    pub fn invariant(self) -> bool {
        pearlite! { false }
    }
}

#[ensures(result == (&a).invariant())]
pub fn g(a: A) -> bool {
    let _ = a;
    true
}

#[ensures(result == false)]
pub fn caller(a: A) -> bool {
    g(a)
}
