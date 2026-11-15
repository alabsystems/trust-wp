//@ expect: verify
//@ xfail: the non-final child's final value is not tied to its resolve-time current (b1 resolves to 5 before *bor = 1); pre-existing incompleteness — inconclusive before and after d245d8b
//@ mechanism: control for h_final_prophecy_store_* — the TRUE claim about the non-final reborrow's final value
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn final_is_5(bor: &mut i32) {
    let b1 = &mut *bor;
    *b1 = 5;
    *bor = 1;
    proof_assert!((^b1)@ == 5);
}
