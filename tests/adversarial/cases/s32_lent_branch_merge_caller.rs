//@ expect: reject
//@ mechanism: a &mut param lent through a branch merge kept the merged identity final; the false callee contract then licensed a false caller assertion
//@ fixed-by: s32 lent-borrow premise removal (535419a)
//@ accept-means: the caller proves `b == 5` after writing 6 through the returned borrow of `b`
//@ teeth: skeptic probe P9e (callee verified strict before 535419a); rejected after
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^b == *b)]
pub fn p9b<'a>(toggle: bool, a: &'a mut i32, b: &'a mut i32) -> &'a mut i32 {
    if toggle { a } else { b }
}

pub fn p9e_caller() {
    let mut a = 10i32;
    let mut b = 5i32;
    let x = p9b(false, &mut a, &mut b);
    *x = 6i32;
    proof_assert!(b == 5i32);
}
