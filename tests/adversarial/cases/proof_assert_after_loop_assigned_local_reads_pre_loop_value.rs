//@ expect: reject
//@ mechanism: the whole-local spelling of proof_assert_after_loop_field_write_reads_loop_exit_value.rs: a program function sets a local `t` to `0`, runs an annotated loop that never touches it, assigns its input `x` to `t` and asserts `t == 0`. The assertion is proved, so the `proof_assert!` lane after a loop is not confined to a field write: it keeps the fact `t == 0` from before the loop and the fact `t == x` from after it under one name, which together say `x == 0` (proof_assert_after_loop_assigned_local_derives_input_fact.rs proves exactly that). The same function without the loop is refuted. Found probing sideways from D-165, which closes this reading for `result` and leaves this lane unchanged.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means an assertion after a loop reads each local at the value the code before the assertion leaves it, under a name no earlier fact shares.
//@ accept-means: an assertion that fails for every nonzero input is credited, and the crate exits 0.
//@ WHY IT IS FALSE: `prog(0, 1)` leaves `t == 1`.
//@ teeth: MEASURED ACCEPTED, exit 0, at the campaign tip and with D-165: `trust-wp: proof_assert in creusot_test::prog verified ✓`, `trust-wp: prog verified ✓ (loop invariant + call obligations)`. Without the loop the same body is `FAILED`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn prog(n: u32, x: u32) {
    let mut t = 0u32;
    let mut i = 0;
    #[invariant(i <= n)]
    while i < n {
        i += 1;
    }
    t = x;
    proof_assert!(t == 0u32);
}
