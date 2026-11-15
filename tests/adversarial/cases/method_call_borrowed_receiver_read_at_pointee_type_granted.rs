//@ expect: reject
//@ mechanism: `(&a).invariant()` with `a: A`. Rust's method lookup starts at the receiver's type,
//@ mechanism: `&A`, where the prelude's `Invariant` (`impl<T: ?Sized> Invariant for &T`, default body
//@ mechanism: `true`) applies by value, and selects it before it derefs to `A` and its inherent
//@ mechanism: `invariant` (false). The contract parser keeps a borrow no `*` reads through as its
//@ mechanism: operand, so the receiver reaches the logic-function resolver as `a`, typed `A`: its
//@ mechanism: method lookup (`method_lookup::selects_only`) sees no `&A` step and takes the inherent
//@ mechanism: `A::invariant` (false). `f`, which returns false, is credited.
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

#[ensures(result == (&a).invariant())]
pub fn f(a: A) -> bool {
    let _ = a;
    false
}
