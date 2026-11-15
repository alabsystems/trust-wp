//@ expect: reject
//@ mechanism: method_call_inherent_program_method_read_as_logic_trait_impl_granted.rs with the receiver
//@ mechanism: `w.0`, which the driver does not type: the encoder's receiver dispatch takes the one
//@ mechanism: logic member for `S` (`<S as Tr>::m`, 10) where Rust's lookup gives the inherent
//@ mechanism: program method (0).
//@ fixed-by: D-196 — the encoder dispatches a receiver to an impl member only where Rust's method
//@ fixed-by: lookup at that self type, or a reference to it, selects nothing else (`receiver_dispatch`).
//@ accept-means: `f` claims `result == w.0.m()` (0), returns 10, and the crate exits 0.
//@ teeth: MEASURED: ACCEPTED at exit 0 (`f verified ✓`) with D-195 in force.
//@ teeth: With D-196: `unknown` (`... Rust's method lookup on that receiver may select another
//@ teeth: method named `m``).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[derive(Clone, Copy)]
pub struct S;

pub trait Tr {
    #[logic]
    fn m(self) -> u32;
}
impl Tr for S {
    #[logic(open)]
    fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}

impl S {
    pub fn m(self) -> u32 {
        0
    }
}

pub struct Wrap(pub S);

#[ensures(result == w.0.m())]
pub fn f(w: Wrap) -> u32 {
    10
}
