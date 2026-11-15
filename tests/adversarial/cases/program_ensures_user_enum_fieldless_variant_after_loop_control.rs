//@ expect: verify
//@ mechanism: a user enum's second field-less variant returned after an annotated loop is that variant. `unknown` at the campaign tip, where the post-loop walk read `E::B` as the unit value every field-less variant shares.
//@ accept-means: n/a (control) — the postcondition holds wherever `prog` may be called.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub enum E {
    A,
    B,
}

#[ensures(match result { E::A => false, E::B => true })]
pub fn prog(n: u32) -> E {
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    E::B
}
