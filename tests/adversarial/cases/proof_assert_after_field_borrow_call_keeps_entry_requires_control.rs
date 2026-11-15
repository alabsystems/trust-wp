//@ expect: verify
//@ mechanism: control for proof_assert_after_field_borrow_call_keeps_entry_requires: the call borrows `p.b`, not `p.a`, so the precondition about `p.a` still holds at the assertion.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct P {
    pub a: u32,
    pub b: u32,
}

#[ensures(true)]
pub fn set7(q: &mut u32) {
    *q = 7;
}

#[requires(p.a@ == 3)]
#[ensures(true)]
pub fn k(mut p: P) -> u32 {
    set7(&mut p.b);
    proof_assert!(p.a@ == 3);
    0
}
