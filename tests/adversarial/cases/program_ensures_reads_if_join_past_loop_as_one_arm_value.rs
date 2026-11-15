//@ expect: reject
//@ mechanism: `let m = if c { 1u32 } else { 2u32 }`, an annotated loop that leaves `m` alone, then `m` is
//@ mechanism: returned under `ensures(result == 2u32)`. The loop lane's depth-first entry walk bound `m` to the
//@ mechanism: value of the arm it walked last, and a binding of a local the loop leaves alone becomes an inferred
//@ mechanism: equality invariant (`infer_stable_loop_invariants`, Rule 1) that the code after the loop assumes.
//@ accept-means: a function that returns 1 on one path is credited with returning 2, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(true)` returns 1.
//@ fixed-by: D-243: the loop lane states no entry value for a local set on one path
//@ fixed-by: (`pre_loop_extract::drop_bindings_set_on_one_path`); the block-slice walker states it at the loop's
//@ fixed-by: entry as a join symbol defined arm by arm (`PathBindings::loop_entry_values`).
//@ teeth: ACCEPTED at exit 0 before D-243; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == 2u32)]
pub fn f(c: bool) -> u32 {
    let m = if c { 1u32 } else { 2u32 };
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3 {
        i += 1;
    }
    m
}
