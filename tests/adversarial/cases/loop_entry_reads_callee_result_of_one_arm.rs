//@ expect: reject
//@ mechanism: `let mut m = 2u32; if c { m = one(); }` before an annotated loop whose invariant reads
//@ mechanism: `m == 1u32`, the postcondition of `one`. The loop lane's entry walk resolved the call on one arm
//@ mechanism: and stated its postcondition about `m` at the loop's entry on both paths.
//@ accept-means: an invariant is initiated from a callee's postcondition established on one arm only, and the
//@ accept-means: crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(false)` enters the loop with `m == 2`.
//@ also-verified: one
//@ fixed-by: D-243: a pre-loop call whose destination is set on one path to the header states no fact at the
//@ fixed-by: loop's entry (`loops::extract_loop_body`, `drop_bindings_set_on_one_path`).
//@ teeth: `error` before D-243, not a named refusal; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 1u32)]
pub fn one() -> u32 {
    1
}

pub fn f(c: bool) {
    let mut m = 2u32;
    if c {
        m = one();
    }
    let mut i = 0u32;
    #[invariant(m == 1u32)]
    while i < 3 {
        i += 1;
    }
}
