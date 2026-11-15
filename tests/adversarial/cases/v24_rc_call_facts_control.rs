//@ expect: verify
//@ mechanism: control for v24_call_result_fact_reads_its_operand_at_the_assertion.rs and
//@ mechanism: v24_ptr_eq_of_two_allocations_holding_one_value.rs: a clone's value at an assertion
//@ mechanism: nothing re-binds (rcc), and `ptr_eq` of allocations holding different values (rcd).
//@ accept-means: n/a (control) - both assertions hold.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use ::std::rc::Rc;
use creusot_std::prelude::*;

pub fn rcc() {
    let r = Rc::new(1i32);
    let r2 = r.clone();
    proof_assert!(r == r2);
}

pub fn rcd() {
    let r = Rc::new(1i32);
    let r2 = Rc::new(2i32);
    let b = Rc::ptr_eq(&r, &r2);
    proof_assert!(!b);
}
