//@ expect: reject
//@ mechanism: the same fn-pointer call in an ANNOTATED loop — cross-lane control for the shared classifier
//@ fixed-by: s62 (wp-s62, shared loop-call-target classification)
//@ accept-means: the annotated lane lost the unresolved-callee refusal it already had before s62.
//@ verdict: failed
//@ fn-failed: evil
//@ teeth: rejected on wp-campaign 04fc8074 already (loop_body.rs owed `false`); pins the behaviour the unannotated lane was missing.
//@ also-verified: needs_positive
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x > 0u32)]
#[ensures(result == x)]
pub fn needs_positive(x: u32) -> u32 {
    x
}

// Identical to s62_fnptr_unannotated_loop except for the invariant, which
// routes the function through the annotated loop lane.
#[ensures(result == 7u32)]
pub fn evil() -> u32 {
    let f: fn(u32) -> u32 = needs_positive;
    let mut i = 0u32;
    #[invariant(true)]
    while i < 1u32 {
        let _unused = f(0u32);
        i += 1u32;
    }
    7u32
}
