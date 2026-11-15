//@ expect: verify
//@ xfail: a tuple's sort carries no component types, so `^` of a tuple element taken through a
//@ xfail: reference is refused wherever it sits: `^((*x).0)` of `x: &mut (i32, i32)` since D-127,
//@ xfail: and `^((*x).q.0)` of a tuple field of a struct since D-128 (verified before). Retiring it
//@ xfail: needs the tuple sort, or the declaration's field, to carry the components' types.
//@ mechanism: the price of D-128's typed projection chain, kept visible: a refusal of a true claim,
//@ mechanism: never a credit.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct P {
    pub q: (i32, i32),
}

#[ensures(^r == 7i32)]
pub fn set7(r: &mut i32) {
    *r = 7i32;
}

#[ensures((^x).q.0 == 7i32)]
pub fn nested_tuple_reborrow(x: &mut P) {
    set7(&mut x.q.0);
}

#[ensures((^x).0 == 7i32)]
pub fn tuple_reborrow(x: &mut (i32, i32)) {
    set7(&mut x.0);
}
