//@ expect: reject
//@ mechanism: the EMPTY self-spec s80 injects for a contract-less recursive function must leave the self-call's RESULT unconstrained — the caller may not read the callee's body through it
//@ accept-means: the self-spec leaked the body: `rec_five(n-1) == 5` is true at runtime but is a theorem of the BODY, not of the (empty) contract, so proving it means the self-call was inlined or its result bound to the returning branch
//@ fixed-by: n/a — s80 FALSE-ACCEPT gate for the route the front took
//@ verdict: failed
//@ teeth: MEASURED both sides. Pre-fix the proof_assert also failed, but for the wrong reason (the fabricated `requires(false)` poisoned everything); post-fix it fails because the empty self-spec constrains nothing. A companion probe over a recursive accumulator (`proof_assert!(*acc == 12345u32)`) shows the lane is not vacuous: it answers `unknown` there.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[check(terminates)]
#[variant(n)]
pub fn rec_five(n: i32) -> i32 {
    if n <= 0 {
        5
    } else {
        let r = rec_five(n - 1);
        // TRUE at runtime, but NOT a consequence of `rec_five`'s (empty)
        // contract. Provable only if the self-call leaked its body.
        proof_assert!(r == 5i32);
        r
    }
}
