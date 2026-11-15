//@ expect: verify
//@ mechanism: control for v14_element_final_of_a_held_borrow_in_a_proof_assert and its siblings: a
//@ mechanism: final read whose operand IS a borrow named as one (a local reborrow of a parameter, the
//@ mechanism: parameter itself under a field projection of its final value) keeps its reading in a
//@ mechanism: `proof_assert!`; D-129 refuses only an operand no name denotes as a borrow (a field, an
//@ mechanism: element, a view, a value a call computes), and `(^x).a` reads `^` of `x` itself.
//@ fixed-by: n/a (over-refusal guard)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S {
    pub a: i32,
}

pub fn reborrow_final(x: &mut i32) {
    let r = &mut *x;
    *r = 5i32;
    proof_assert!(^r == 5i32);
}

pub fn final_field_scalar(x: &mut S) {
    x.a = 5i32;
    proof_assert!((^x).a == 5i32);
}
