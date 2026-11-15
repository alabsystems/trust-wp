//@ expect: reject
//@ mechanism: The generic spelling of ensures_shared_ref_receiver_and_its_deref_read_as_one_call.rs: with
//@ mechanism: `T: Tr` and `&T: Tr`, Rust reads `x.m()` as `<T as Tr>::m(x)` and `(&x).m()` as
//@ mechanism: `<&T as Tr>::m(&x)`; the two reach the postcondition's reflexive check as one term and `g` is
//@ mechanism: credited with no solver query.
//@ accept-means: a postcondition equating two different logic functions' values is credited with no query.
//@ WHY IT IS FALSE: at `T = S` the two are `false` and `true`; Creusot's `vc_g` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0 (`g verified ✓`, no solver query) with D-163 and D-164 in force, and at
//@ teeth: the campaign tip.
//@ fixed-by: OPEN — committed RED rather than hidden (see the concrete spelling).
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

#[ensures(x.m() == (&x).m())]
pub fn g<T: Tr>(x: T)
where
    for<'a> &'a T: Tr,
{
}
