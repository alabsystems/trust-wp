//@ expect: reject
//@ mechanism: `let mut m = if c { 1u32 } else { 2u32 }; if d { m = 5; loop A } else { loop B }`, both loops
//@ mechanism: claiming `invariant(m <= 2u32)`. Loop A's entry walk passed the arms of the first `if` after
//@ mechanism: `m = 5` in its depth-first order and initiated A's invariant from an arm's value.
//@ accept-means: an invariant is credited as initiated on a path that enters the loop with `m == 5`, and the
//@ accept-means: crate exits 0.
//@ WHY THE CONTRACT IS FALSE: `f(true, true)` enters loop A with `m == 5`.
//@ fixed-by: D-243: the loop lane states no entry value for a local set on one path
//@ fixed-by: (`pre_loop_extract::drop_bindings_set_on_one_path`); the block-slice walker states it at the loop's
//@ fixed-by: entry as a join symbol defined arm by arm (`PathBindings::loop_entry_values`).
//@ teeth: ACCEPTED at exit 0 before D-243; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f(c: bool, d: bool) {
    let mut m = if c { 1u32 } else { 2u32 };
    if d {
        m = 5;
        let mut i = 0u32;
        #[invariant(m <= 2u32)]
        while i < 3 {
            i += 1;
        }
    } else {
        let mut j = 0u32;
        #[invariant(m <= 2u32)]
        while j < 3 {
            j += 1;
        }
    }
}
