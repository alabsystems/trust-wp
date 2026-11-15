//@ expect: reject
//@ mechanism: prophecy-store — loop-invariant initialization reads *bor at its entry binding although it was stored before the loop
//@ accept-means: invariant (*bor)@ == 0 credited at loop entry although *bor is 5
//@ teeth: verified on wp-s30 aae5ef9
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*bor)@ == 0)]
pub fn loop_inv_entry(bor: &mut i32) {
    *bor = 5;
    let mut i = 0;
    #[invariant((*bor)@ == 0)]
    while i < 3 {
        i += 1;
    }
}
