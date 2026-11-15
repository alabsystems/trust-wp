//@ expect: reject
//@ mechanism: `S::call_0` resolved to the bare call-result symbol `call_0`.
//@ fixed-by: wp-s28 (synthesized_names `$` namespace)
//@ accept-means: g proved result == 99 for an arbitrary x.
//@ teeth: exit-0 false accept on the wp-campaign merge 22198c14 (rv8/ac1); FAILED on the fix.
//@ also-verified: id
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S;
impl S {
    #[allow(non_upper_case_globals)]
    pub const call_0: u32 = 99;
}

#[ensures(result == v)]
pub fn id(v: u32) -> u32 { v }

// WRONG: returns x, which is arbitrary.
#[requires(S::call_0 == 99u32)]
#[ensures(result == 99u32)]
pub fn g(x: u32) -> u32 { id(x) }
