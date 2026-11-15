//@ expect: reject
//@ mechanism: the safe-Rust twin of v8_callsite_lent_into_raw_pointer: `Rc<i32>` reaches a raw
//@ mechanism: pointer through its fields, so `mut_borrow::lent` reads `p` as lent into the result
//@ mechanism: (`Rc::new(*p)` flows from `p`); the call saw no region in `Rc<i32>` and read the
//@ mechanism: pre-Creusot `*p` as `^p`.
//@ accept-means: a caller is credited with a reading of a callee clause its lane did not prove.
//@ WHY THE CONTRACT IS FALSE: `share` stores 5 through the borrow of `x`, so `^x` is 5 and the
//@ WHY THE CONTRACT IS FALSE: precondition makes the entry `*x` something else.
//@ fixed-by: D-102
//@ teeth: MEASURED on cbadb52d (debug driver): `share_caller verified`; d454c1e1: unknown. On the
//@ teeth: D-102 tree: share refused, caller unknown.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::rc::Rc;

use creusot_std::prelude::*;

#[ensures(*p == old(*p))]
pub fn share(p: &mut i32) -> Rc<i32> {
    *p = 5;
    Rc::new(*p)
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn share_caller(x: &mut i32) {
    let _ = share(x);
}
