//@ expect: verify
//@ mechanism: a user enum's second variant returned after an annotated loop is that variant. FAILED with a counterexample at the campaign tip, where the post-loop walk read `E::Y(i)` as `i` and the datatype binding wrapped it in the first constructor with a field, `E::X`.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E {
    X(u32),
    Y(u32),
}

#[ensures(match result { E::X(_) => false, E::Y(_) => true })]
pub fn prog(n: u32) -> E {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    E::Y(i)
}
