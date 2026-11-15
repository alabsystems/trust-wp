//@ expect: reject
//@ mechanism: method_call_trait_default_read_as_out_of_scope_impl_granted.rs with a receiver the driver
//@ mechanism: does not type (`w.0`): the call reaches the ENCODER unresolved, and its dispatch
//@ mechanism: (`resolve_family_by_receiver`) takes the one impl member whose nominal sort is `S`,
//@ mechanism: `<S as other::Tr2>::m` (0), where Rust's lookup gives Tr1's default (10).
//@ fixed-by: D-196 — the encoder dispatches a receiver to an impl member only where Rust's method
//@ fixed-by: lookup at that self type, or a reference to it, selects nothing else (`receiver_dispatch`).
//@ accept-means: `f` claims `result == w.0.m()` (10), returns 0, and the crate exits 0.
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

pub trait Tr1 {
    #[logic(open)]
    fn m(self) -> u32 {
        pearlite! { 10u32 }
    }
}
impl Tr1 for S {}

pub mod other {
    use super::*;
    pub trait Tr2 {
        #[logic]
        fn m(self) -> u32;
    }
    impl Tr2 for S {
        #[logic(open)]
        fn m(self) -> u32 {
            pearlite! { 0u32 }
        }
    }
}

pub struct Wrap(pub S);

#[ensures(result == w.0.m())]
pub fn f(w: Wrap) -> u32 {
    0
}
