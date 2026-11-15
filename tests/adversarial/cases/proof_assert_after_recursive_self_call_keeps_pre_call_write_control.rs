//@ expect: verify
//@ mechanism: control for proof_assert_after_recursive_self_call_keeps_pre_call_write: the assertion comes BEFORE the self-call, so `*acc == n` is true and provable.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(terminates)]
#[variant(n)]
pub fn rec_set(n: u32, acc: &mut u32) {
    if n > 0 {
        *acc = n;
        proof_assert!(*acc == n);
        rec_set(0, acc);
    } else {
        *acc = 0;
    }
}
