//@ expect: verify
//@ mechanism: control for proof_assert_after_reborrow_call_keeps_pre_call_write: the same call and the same assertion, with the write AFTER the call, so `*acc == 2` is true and provable.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn set1(q: &mut u32) {
    *q = 1;
}

#[ensures(true)]
pub fn f(acc: &mut u32) {
    set1(acc);
    *acc = 2;
    proof_assert!(*acc == 2u32);
}
