//@ expect: reject
//@ mechanism: the `if`/`else` spelling of loop_entry_reads_if_join_as_one_arm_value.rs: `let m; if c { m = 1 }
//@ mechanism: else { m = 2 }`; the loop lane's depth-first entry walk read the invariant's initiation at the value
//@ mechanism: of the arm it walked last.
//@ accept-means: an invariant that holds at the loop's entry on one path only is credited as initiated, and the
//@ accept-means: crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(true)` enters the loop with `m == 1`.
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
    let m;
    if c {
        m = 1u32;
    } else {
        m = 2u32;
    }
    let mut i = 0u32;
    #[invariant(m == 2u32)]
    while i < 3 {
        i += 1;
    }
}
