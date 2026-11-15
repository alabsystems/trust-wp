//@ expect: reject
//@ mechanism: a &mut param lent into the return value kept a final_values entry asserted as ^p == <entry> (aggregate (b, 1))
//@ fixed-by: s32 lent-borrow premise removal (535419a)
//@ accept-means: the callee pins a prophecy the caller owns (the caller can write through result)
//@ teeth: VERIFIED (strict, hole-free) before 535419a per the materialized-gates audit + skeptic; rejected after
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^b == *b)]
pub fn p12<'a>(b: &'a mut i32) -> (&'a mut i32, i32) {
    (b, 1i32)
}
