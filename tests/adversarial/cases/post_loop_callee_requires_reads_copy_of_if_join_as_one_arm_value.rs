//@ expect: reject
//@ mechanism: `let mut m = 1u32; if c { n = 1 } else { m = 2 }; let j = m;` before an annotated loop, then
//@ mechanism: `need(j)` after it under `requires(k == 1u32)`. `j` is assigned on every path, but from a local
//@ mechanism: set on one: the loop lane's depth-first entry walk bound `j` through the value of the arm it walked
//@ mechanism: last, and that binding, an inferred equality invariant of the loop (`infer_stable_loop_invariants`,
//@ mechanism: Rule 1), discharged the call after the loop.
//@ accept-means: a callee's precondition is discharged with the value one arm gives while the other arm gives
//@ accept-means: another, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(false)` calls `need(2)`.
//@ also-verified: need
//@ fixed-by: D-243: a binding computed from a local set on one path is dropped with it
//@ fixed-by: (`pre_loop_extract::drop_bindings_set_on_one_path`); the block-slice walker states `j` at the
//@ fixed-by: loop's entry as the join symbol of `m`, defined arm by arm (`PathBindings::loop_entry_values`).
//@ teeth: ACCEPTED at exit 0 before D-243; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k == 1u32)]
pub fn need(k: u32) {}

pub fn f(c: bool) {
    let mut n = 0u32;
    let mut m = 1u32;
    if c {
        n = 1;
    } else {
        m = 2;
    }
    let j = m;
    #[invariant(n <= 3u32)]
    while n < 3 {
        n += 1;
    }
    need(j);
}
