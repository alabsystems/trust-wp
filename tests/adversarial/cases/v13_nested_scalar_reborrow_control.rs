//@ expect: verify
//@ mechanism: control for v13_nested_final_of_a_held_borrow_in_a_proof_assert: a reborrow of a
//@ mechanism: scalar two fields deep (`&mut x.s.a`) reaches the callee's `^r` as `^((*x).s.a)`,
//@ mechanism: whose chain the declarations type down to an `i32`, so it keeps Creusot's rule
//@ mechanism: `^(x.s.a) == (^x).s.a`. D-128 refuses a chain whose field may be a mutable reference,
//@ mechanism: not every chain.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S {
    pub a: i32,
    pub b: i32,
}

pub struct NS {
    pub s: S,
    pub c: i32,
}

#[ensures(^r == 7i32)]
pub fn set7(r: &mut i32) {
    *r = 7i32;
}

#[ensures((^x).s.a == 7i32)]
pub fn nested_scalar_reborrow(x: &mut NS) {
    set7(&mut x.s.a);
}
