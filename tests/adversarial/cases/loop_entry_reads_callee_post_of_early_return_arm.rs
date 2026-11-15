//@ expect: reject
//@ mechanism: `if c { below(x); return; }` before an annotated loop whose invariant reads `x@ < 100`, the
//@ mechanism: postcondition of `below`. The loop lane resolved every pre-loop call its entry walk met
//@ mechanism: (`resolve_pre_loop_call_facts_with_spec_ctx`), including one on an arm that returns before the
//@ mechanism: loop, and stated its postcondition at the loop's entry.
//@ accept-means: an invariant is initiated from a callee's postcondition established only on a path that never
//@ accept-means: reaches the loop, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(100, false)` enters the loop with `x == 100`.
//@ also-verified: below
//@ fixed-by: D-243: a pre-loop call whose destination, receiver or argument is set on one path to the header
//@ fixed-by: states no fact at the loop's entry (`loops::extract_loop_body`, `drop_bindings_set_on_one_path`).
//@ teeth: ACCEPTED at exit 0 before D-243; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(x@ < 100)]
pub fn below(x: u32) {
    #[invariant(true)]
    while x >= 100 {}
}

pub fn f(x: u32, c: bool) {
    if c {
        below(x);
        return;
    }
    let mut i = 0u32;
    #[invariant(x@ < 100)]
    while i < 3 {
        i += 1;
    }
}
