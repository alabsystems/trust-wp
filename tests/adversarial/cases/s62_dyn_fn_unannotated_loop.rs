//@ expect: reject
//@ mechanism: a `dyn Fn` call inside a loop carrying NO #[invariant] has no unique target
//@ fixed-by: s62 (wp-s62, shared loop-call-target classification)
//@ accept-means: a vtable-dispatched callee in an unannotated loop owed nothing.
//@ verdict: failed
//@ fn-failed: evil_dyn
//@ teeth: rejected on wp-campaign 04fc8074 too (the Fn::call path refused it there); kept as the `dyn` twin of the fn-pointer case.
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

#[ensures(result == 7u32)]
pub fn evil_dyn() -> u32 {
    let f: &dyn Fn(u32) -> u32 = &(needs_positive as fn(u32) -> u32);
    let mut i = 0u32;
    while i < 1u32 {
        let _unused = f(0u32);
        i += 1u32;
    }
    7u32
}
