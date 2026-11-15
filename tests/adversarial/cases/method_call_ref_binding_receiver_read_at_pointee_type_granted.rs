//@ expect: reject
//@ mechanism: method_call_borrowed_receiver_read_at_pointee_type_granted.rs through a binding by
//@ mechanism: reference: `let ref r = a; r.invariant()`. `r: &A`, so Rust selects `<&A as
//@ mechanism: Invariant>::invariant` (true). The parser binds `r` to `a` at no reference level, the
//@ mechanism: resolver types it `A`, and reads the inherent `A::invariant` (false): `f`, which returns
//@ mechanism: false, is credited.
//@ fixed-by: D-201 — REFUSED: the contract parser spells a method call whose receiver has a
//@ fixed-by: reference level it drops with the refusal marker (`resolve_method_call`), whatever
//@ fixed-by: the call names.
//@ accept-means: `f` claims `result == true` in Rust's reading, returns false, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-199 in force.
//@ teeth: With D-201: REFUSED (`unknown`): `f` errors on the unresolved marker
//@ teeth: `__lfidU__invariant`.
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

#[ensures(result == pearlite! { let ref r = a; r.invariant() })]
pub fn f(a: A) -> bool {
    let _ = a;
    false
}
