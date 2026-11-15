//@ expect: reject
//@ mechanism: a &mut param lent into the return value kept a final_values entry asserted as ^p == <entry> (branch over two field reborrows)
//@ fixed-by: s32 lent-borrow premise removal (535419a)
//@ accept-means: the callee pins a prophecy the caller owns (the caller can write through result)
//@ teeth: rejected after 535419a (new shape, not probed before)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^x == *x)]
pub fn ftoggle<'a>(t: bool, x: &'a mut (i32, i32)) -> &'a mut i32 {
    if t { &mut x.0 } else { &mut x.1 }
}
