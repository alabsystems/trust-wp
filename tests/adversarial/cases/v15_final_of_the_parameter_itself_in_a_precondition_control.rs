//@ expect: verify
//@ mechanism: the boundary of D-183: `^x` of a `&mut` parameter's own name is the final value of the
//@ mechanism: borrow the function holds, which its body decides; a precondition may read it.
//@ accept-means: (control) a precondition over the parameter's own final value still verifies.
//@ teeth: MEASURED (debug driver, ay 561e68c7c): verified on f214082f and with D-183.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(^x == k)]
#[ensures(k == 5i32)]
pub fn req_whole(x: &mut i32, k: i32) {
    *x = 5i32;
}
