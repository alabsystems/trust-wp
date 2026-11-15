//@ expect: reject
//@ mechanism: result_final bound to transform(tuple_get_1(x)) == the current term for a returned field reborrow
//@ fixed-by: s32 lent-borrow premise removal (535419a)
//@ accept-means: *result == ^result made provable for a returned field reborrow
//@ teeth: VERIFIED (strict, hole-free) before 535419a per the materialized-gates audit + skeptic; rejected after
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(*result == ^result)]
pub fn p2<'a>(x: &'a mut (i32, i32)) -> &'a mut i32 {
    &mut x.1
}
