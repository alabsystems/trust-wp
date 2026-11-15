//@ expect: verify
//@ xfail: the honest twin of s84_local_reborrow_store_return — `result == 7` is refuted today. Measured on 684821d0: FAILED, base_exit_code=1. Retire this xfail when the primary lane routes a store through a local borrow to the borrowed local.
//@ mechanism: control for s84_local_reborrow_store_return — the same program with the true postcondition.
//@ accept-means: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
#[ensures(result == 7i32)]
pub fn k() -> i32 {
    let mut x = 5i32;
    let r = &mut x;
    *r = 7;
    x
}
