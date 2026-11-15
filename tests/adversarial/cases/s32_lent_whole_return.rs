//@ expect: reject
//@ mechanism: a &mut param returned whole keeps no identity final (^x is the caller's prophecy)
//@ fixed-by: s32 lent-borrow premise removal (535419a); control P1 of the materialized-gates audit
//@ accept-means: the callee pins a prophecy the caller owns (the caller can write through result)
//@ teeth: rejected before and after 535419a (P1 was the audit's correctly-failing control); pins it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^x == *x)]
pub fn p1<'a>(x: &'a mut i32) -> &'a mut i32 {
    x
}
