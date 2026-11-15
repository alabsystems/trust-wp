//@ expect: reject
//@ mechanism: the return-expression lane translates a read through a local `&mut` borrow after a store through it (`*r = 7; *r`) as the pointee's ENTRY value. The staleness gate that fails call preconditions closed on exactly this read (`h_stale_deref_store_local_copy`) is not consulted for a read that flows into the return value, so the postcondition is checked against the entry value.
//@ fixed-by: wp-s84 (the return-expression lane fails closed on a value read after a store through a borrow of it — the same staleness gate the call-precondition sink already had)
//@ accept-means: `*r` after `*r = 7` is proved to be the pre-store value in a `#[ensures]` — a plain-Rust false accept; the proof_assert lane gets the same program right.
//@ WHY THE PROGRAM IS WRONG: `*r` is 7 after the store and is returned; `result == 5` is false on every run.
//@ teeth: LIVE on the campaign tip 684821d0: ACCEPTED, `k verified`, base_exit_code=0
//@ teeth: on this `result == 5` spelling; the true twin `result == 7`
//@ teeth: is REFUTED on the same binary, and the proof_assert twins (z_deref_read_pa_*) are both right.
//@ teeth: PRE-EXISTING; found by this front's probes. With the return gate: unknown, exit 2
//@ teeth: on the identical program.
//@ verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
#[ensures(result == 5i32)]
pub fn k() -> i32 {
    let mut x = 5i32;
    let r = &mut x;
    *r = 7;
    *r
}
