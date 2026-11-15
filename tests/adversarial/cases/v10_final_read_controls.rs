//@ expect: verify
//@ mechanism: controls for the v10 cases: what D-108 refuses is only a read of a final value no
//@ mechanism: lane may state. A logic function reading no final value keeps its unfolding in a
//@ mechanism: crate that withdraws another; a `&mut` beside one over a cell keeps its final value;
//@ mechanism: a projection slot is read as its normalized type, so a borrow no slot can hold is
//@ mechanism: not lent (`slot_only`), and two `&mut` of one lifetime lend nothing to each other.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use std::cell::Cell;

use creusot_std::prelude::*;

#[logic(open, prophetic)]
pub fn unchanged(q: &mut i32) -> bool {
    pearlite! { ^q == *q }
}

#[logic(open)]
pub fn succ(x: i32) -> Int {
    pearlite! { x@ + 1 }
}

#[requires(*p < 100i32)]
#[ensures((^p)@ == succ(*p))]
pub fn inc_beside(p: &mut i32) {
    *p += 1;
}

#[requires(*n < 100i32)]
#[ensures(^n == *n + 1i32)]
pub fn inc_beside_cell(n: &mut i32, x: &mut Cell<i32>) {
    *n += 1;
}

pub trait Tr<'a> {
    type Slot;
}

impl<'a> Tr<'a> for () {
    type Slot = Option<&'a mut i32>;
}

#[ensures(^slot == *slot)]
pub fn slot_only<'a>(p: &'a mut i32, slot: &mut <() as Tr<'a>>::Slot) {}

#[requires(*a < 100i32)]
#[ensures(^a == *a + 1i32 && ^b == *b)]
pub fn two<'a>(a: &'a mut i32, b: &'a mut i32) {
    *a += 1;
}
