//@ expect: verify
//@ mechanism: the control for the const_short_name_* cases: one constant `K`, spelled bare by a
//@ mechanism: postcondition, a precondition, a logic function, a loop invariant and a proof assertion,
//@ mechanism: and read through an import in another module. Every spelling has that one meaning, so
//@ mechanism: its value stands in for it everywhere.
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub const K: u32 = 10;

#[logic(open)]
pub fn kk() -> u32 {
    K
}

#[ensures(result == K)]
pub fn f() -> u32 {
    10
}

#[ensures(result == 10u32)]
pub fn g() -> u32 {
    f()
}

#[requires(x == K)]
#[ensures(result == kk())]
pub fn h(x: u32) -> u32 {
    x
}

#[ensures(result == 10u32)]
pub fn j() -> u32 {
    let mut i = 0u32;
    #[invariant(i <= K)]
    while i < 10 {
        i += 1;
    }
    proof_assert!(i == K);
    i
}

#[ensures(result == 10u32)]
pub fn j2() -> u32 {
    h(10)
}

pub mod b {
    use creusot_std::prelude::*;
    use crate::K;
    #[ensures(result == K)]
    pub fn f2() -> u32 {
        10
    }
}
