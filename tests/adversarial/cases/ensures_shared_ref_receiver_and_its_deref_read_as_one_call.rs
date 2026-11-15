//@ expect: reject
//@ mechanism: `Tr` is implemented for `S` and for `&S`. On `x: &S`, Rust's method probe reads `x.m()` at the
//@ mechanism: receiver's own type, `<&S as Tr>::m(x)`, and `(*x).m()` at `S`, `<S as Tr>::m(*x)`. The
//@ mechanism: typed lookup reads neither (`resolved=None`), and the two calls reach the postcondition's
//@ mechanism: reflexive check as one term: `g` is credited with no solver query, so the call the encoder
//@ mechanism: would refuse is never encoded. D-164 gave each REFUSED call a symbol of its own for this
//@ mechanism: reason; two calls that are one term before any resolution are not reached by it.
//@ accept-means: a postcondition equating two different logic functions' values is credited with no query.
//@ WHY IT IS FALSE: `<&S as Tr>::m` is `true` and `<S as Tr>::m` is `false`; Creusot's `vc_g` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0 (`g verified ✓`, no solver query) with D-163 and D-164 in force, and at
//@ teeth: the campaign tip: the typed lookup reads neither call (`resolved=None`), so neither D-163's
//@ teeth: confirmation nor D-164's refusal symbol is reached.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means a method call keeps its receiver's
//@ fixed-by: reference level until the call is resolved, so `x.m()` and `(*x).m()` are different terms.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    fn m(self) -> bool;
}
pub struct S;
impl Tr for S {
    #[logic(open)]
    fn m(self) -> bool {
        false
    }
}
impl<'a> Tr for &'a S {
    #[logic(open)]
    fn m(self) -> bool {
        true
    }
}

#[ensures(x.m() == (*x).m())]
pub fn g(x: &S) {}
