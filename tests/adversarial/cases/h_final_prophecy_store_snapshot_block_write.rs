//@ expect: reject
//@ mechanism: snapshot-capture ignore — a side-effecting snapshot! block writes through the captured &mut; the borrow is not ghost-only, so it must keep b1 non-final
//@ accept-means: (^b1)@ == 1 credited; ^b1 is 5
//@ teeth: verified on wp-s30 aae5ef9 (reviewer probe p1)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn snapshot_block_write(bor: &mut i32) {
    let b1 = &mut *bor;
    *b1 = 5;
    let _s = snapshot!({
        let t = &mut *bor;
        *t = 1;
        t
    });
    proof_assert!((^b1)@ == 1);
}
