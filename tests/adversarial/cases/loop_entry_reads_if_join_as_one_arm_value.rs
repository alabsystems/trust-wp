//@ expect: reject
//@ mechanism: `let mut m = 1u32; if c { m = 2 }` before an annotated loop whose invariant reads `m`: the loop
//@ mechanism: lane's entry walk (`pre_loop_extract::extract_pre_loop_assignments`) walks depth-first and keeps
//@ mechanism: the last translatable assignment it meets, so the arm it walked last stood for both paths and the
//@ mechanism: invariant's initiation read `m == 2`. The D-243 residual.
//@ accept-means: an invariant that holds at the loop's entry on one path only is credited as initiated, and the
//@ accept-means: crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(false)` enters the loop with `m == 1`.
//@ fixed-by: D-243: the loop lane states no entry value for a local set on one path
//@ fixed-by: (`pre_loop_extract::drop_bindings_set_on_one_path`); the block-slice walker states it at the loop's
//@ fixed-by: entry as a join symbol defined arm by arm (`PathBindings::loop_entry_values`).
//@ teeth: ACCEPTED at exit 0 before D-243; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(c: bool) {
    let mut m = 1u32;
    if c {
        m = 2;
    }
    let mut i = 0u32;
    #[invariant(m == 2u32)]
    while i < 3 {
        i += 1;
    }
}
