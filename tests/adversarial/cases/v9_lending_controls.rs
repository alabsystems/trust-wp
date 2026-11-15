//@ expect: verify
//@ mechanism: control for the v9 lending and interior-mutability cases: two `&mut` parameters
//@ mechanism: of one named lifetime whose referents hold no borrow lend nothing to each other
//@ mechanism: (`swap_old`), a generic swap lends nothing (a type parameter is no slot for a
//@ mechanism: late-bound lifetime, which no bound can name), and a reborrow of a reborrow passed to
//@ mechanism: a callee whose clause states its final value is credited with it.
//@ fixed-by: n/a (over-refusal guard for D-107)
//@ teeth: MEASURED (debug driver) on 576532d7: `inc_caller_reborrow vacuous (contradictory
//@ teeth: premises)` (the two-phase writeback fused the outer reborrow's entry value with the
//@ teeth: callee's final); on the D-107 tree all five verified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(*a == old(*b) && *b == old(*a))]
pub fn swap_old<'a>(a: &'a mut i32, b: &'a mut i32) {
    let t = *a;
    *a = *b;
    *b = t;
}

#[ensures(^a == *b && ^b == *a)]
pub fn swap_generic<T>(a: &mut T, b: &mut T) {
    std::mem::swap(a, b);
}

#[ensures(^a == *b && ^b == *a)]
pub fn swap_generic_named<'a, T>(a: &'a mut T, b: &'a mut T) {
    std::mem::swap(a, b);
}

#[requires(*p < 100i32)]
#[ensures(^p == *p + 1i32)]
pub fn inc(p: &mut i32) {
    *p += 1;
}

#[requires(*x < 100i32)]
#[ensures(^x == *x + 1i32)]
pub fn inc_caller_reborrow(x: &mut i32) {
    inc(&mut *x);
}
