//@ expect: reject
//@ mechanism: prophecy-store — non-final reborrow final value taken from the parent's final value after a direct parent store
//@ accept-means: (^b1)@ == 1 credited; the value written through b1 (and so ^b1) is 5
//@ teeth: verified on wp-s30 aae5ef9 (pre-fix); rejected after d245d8b
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn direct_store(bor: &mut i32) {
    let b1 = &mut *bor;
    *b1 = 5;
    *bor = 1;
    proof_assert!((^b1)@ == 1);
}
