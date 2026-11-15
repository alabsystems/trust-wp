//@ expect: verify
//@ mechanism: control: a by-value field read lends nothing; ^x == *x stays provable
//@ fixed-by: s32 lent-borrow premise removal (535419a)
//@ accept-means: n/a (control)
//@ teeth: verified after 535419a
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == (*x).1 && ^x == *x)]
pub fn bvf(x: &mut (i32, i32)) -> i32 {
    x.1
}
