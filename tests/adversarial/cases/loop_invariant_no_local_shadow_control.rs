//@ expect: verify
//@ mechanism: control: the same invariant with no local `k`: `k()` is the crate root's logic function
//@ mechanism: (10) and the invariant holds. A refusal of loop_invariant_local_closure_call_granted.rs
//@ mechanism: must be keyed on the local binding.
//@ fixed-by: n/a (control for loop_invariant_local_closure_call_granted.rs; verified before D-195 and
//@ fixed-by: with it)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> u32 {
    pearlite! { 10u32 }
}

pub fn host() -> u32 {
    let mut i = 0u32;
    #[invariant(k() == 10u32)]
    while i < 3 {
        i += 1;
    }
    i
}
