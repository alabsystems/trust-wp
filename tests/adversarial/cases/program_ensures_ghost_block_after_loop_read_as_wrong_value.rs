//@ expect: reject
//@ mechanism: a `ghost!` block runs an annotated loop and yields `y`, which the loop leaves at `x`, and the postcondition claims `*result` is `x + 1`. The post-loop return walk (`trust-wp-driver` `mir_analysis::loops::post_loop::extract_post_loop_return`) reads `Ghost::new(y)` as `y`; a reading that took the ghost's argument from anywhere else, or left `result` free, would let the false claim through.
//@ accept-means: a function whose ghost holds `x` is credited with a postcondition saying it holds `x + 1`, and the crate exits 0.
//@ WHY IT IS FALSE: `foo(0)` returns a ghost holding `0`, not `1`.
//@ teeth: rejected at the campaign tip and here; at the campaign tip the walk read any unnamed one-argument call as the identity, here only `Ghost::new`/`Snapshot::new` resolved by the impl's self type.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures((*result)@ == x@ + 1)]
pub fn foo(x: u32) -> Ghost<u32> {
    ghost! {
        let mut y = 0;
        let mut i = x;
        #[variant(i)]
        #[invariant(y@ + i@ == x@)]
        while i > 0 {
            i -= 1;
            y += 1;
        }
        y
    }
}
