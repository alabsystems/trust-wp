//@ expect: verify
//@ mechanism: control: method_call_deref_receiver_inherent_beside_reference_blanket_control.rs read at a
//@ mechanism: CALL SITE. `g`'s contract `result == (*a).invariant(b)` is `A::invariant` (`b`), and
//@ mechanism: `caller` claims `result == b` of `g(a, b)`. The callee-text resolver types the receiver
//@ mechanism: `(*a)` as Rust does (`A`), so the call site reads the inherent method.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; MEASURED refused before D-201)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct A {}
impl A {
    #[logic(open)]
    pub fn invariant(self, b: bool) -> bool {
        pearlite! { b }
    }
}

#[ensures(result == (*a).invariant(b))]
pub fn g(a: &mut A, b: bool) -> bool {
    let _ = a;
    b
}

#[ensures(result == b)]
pub fn caller(a: &mut A, b: bool) -> bool {
    g(a, b)
}
