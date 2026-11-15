//@ expect: reject
//@ mechanism: in a function with an annotated loop, the call obligations of the code before the
//@ mechanism: loop come from the block-slice walker (`collect_call_effects_for_blocks`), whose
//@ mechanism: entry walk binds each local in depth-first order and lets a temporary keep the value
//@ mechanism: its operand had when the walk first reached it. `if c { n = 1 } else { i = 0 }` joins
//@ mechanism: before `need7(i)`: the walk reaches the join through the `n = 1` arm first, the copy
//@ mechanism: of `i` the call is handed keeps 7, and the `else` arm's `i = 0` never reaches it.
//@ accept-means: a callee's precondition before a loop was discharged with the value one arm of
//@ accept-means: an `if` leaves while the other arm overwrote it. Concretely: `go(false)` calls
//@ accept-means: `need7(0)`.
//@ also-verified: need7
//@ teeth: the code after a loop is read with the loop-exit names (D-235); before D-243 the code before
//@ teeth: the first loop was read with one binding per local for the whole slice.
//@ fixed-by: D-243: the walker binds locals path by path (`call_effect_paths`); a local the predecessors of a join
//@ fixed-by: bind apart is a symbol of the join, defined arm by arm where the dominating switch tells the arms apart.
//@ teeth: ACCEPTED at exit 0 before D-243; `failed` with D-243.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(k == 7u32)]
pub fn need7(k: u32) {}

pub fn go(c: bool) {
    let mut n = 0u32;
    let mut i = 7u32;
    if c {
        n = 1;
    } else {
        i = 0;
    }
    need7(i);
    #[invariant(n <= 3u32)]
    while n < 3 {
        n += 1;
    }
}
