//@ expect: reject
//@ mechanism: the caller's spelling of logic_fn_body_block_local_name_shadowing_module_name: a contract-free logic function `inner`, declared in a block, calls `k()`, and both the block and the crate root declare a logic function `k`. Rust resolves the call to the block's `k` (10); the identity pass names it by the root's (0). `inner` owes nothing of its own, so no goal of it is refused, and its misread body was the defining axiom a contracted caller unfolds: `outer`'s `result == 0` was proved. The settled body's call has no counterpart in the type-checked form, so the body is misread and hidden (D-136), and `outer` is refuted. Found probing sideways from the resolution record.
//@ accept-means: `outer` claims `result == 0`, returns `inner()`, which is the block's `k()`, 10, and the crate exits 0.
//@ WHY IT IS FALSE: `outer()` is `inner()`, which is `host::k()`, which is 10.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-136's naming of a renamed call in place and its counterpart check on the settled body not yet: `creusot_test::host::outer verified ✓`. At the campaign tip `inner` was left unresolved and the call refused. The control is logic_fn_body_block_local_name_shadowing_read_by_caller_control.rs.
//@ fixed-by: D-136
//@ verdict: error
//@ refused-with: creusot_test::host::outer postcondition FAILED (logic postcondition)
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

    #[logic(open)]
    fn inner() -> Int {
        k()
    }

    #[logic]
    #[ensures(result == 0)]
    fn outer() -> Int {
        inner()
    }

    0
}
