//@ expect: reject
//@ mechanism: a logic function declared in a block calls `k()`, and both that block and the crate root declare a logic function `k`. Rust resolves the call to the block's `k` (10): an item in a block shadows the module's. The identity pass names the call by the root's `k` (0), whose unique id the ensures lane unfolds, so `inner`'s `result == 0` was proved. The body's type-checked form resolves the call to the block's `k`, so the parsed call's id has no counterpart there and the body is refused (D-136). The contract-clause spelling of the same resolver gap is block_local_logic_fn_name_resolved_in_module_granted.rs. Found probing sideways from D-120.
//@ accept-means: `inner` claims `result == 0`, returns the block's `k()`, which is 10, and the crate exits 0.
//@ WHY IT IS FALSE: `inner()` is `host::k()`, which is 10.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::host::inner verified ✓`. The control is logic_fn_body_block_local_name_shadowing_module_name_control.rs.
//@ fixed-by: D-136
//@ verdict: error
//@ refused-with: creusot_test::host::inner postcondition FAILED (logic postcondition)
//@ teeth: since D-174 the identity pass withholds the root's `k` for a name `host`'s body redeclares,
//@ teeth: so the call is read as rustc resolved it, the block's `k`, and `inner`'s false claim is
//@ teeth: refuted. A crate whose only obligation is a logic postcondition reports that refutation as
//@ teeth: an unverified axiom and counts no failure, so the rejection is pinned on its FAILED line.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn k() -> Int {
    pearlite! { 0 }
}

pub fn host() -> u32 {
    #[logic(open)]
    fn k() -> Int {
        pearlite! { 10 }
    }

    #[logic]
    #[ensures(result == 0)]
    fn inner() -> Int {
        k()
    }

    0
}
