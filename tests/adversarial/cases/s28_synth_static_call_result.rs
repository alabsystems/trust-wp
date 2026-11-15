//@ expect: reject
//@ mechanism: static twin of s28_synth_const_call_result.
//@ fixed-by: wp-s28 (synthesized_names `$` namespace)
//@ accept-means: g proved result == 99 for an arbitrary x.
//@ teeth: exit-0 false accept on the wp-campaign merge 22198c14 (rv8/s1); FAILED on the fix.
//@ also-verified: id
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(non_upper_case_globals)]
pub static call_0: u32 = 99;
#[allow(non_upper_case_globals)]
pub static _call_0: u32 = 99;

#[ensures(result == v)]
pub fn id(v: u32) -> u32 { v }

// WRONG: returns x, which is arbitrary.
#[requires(call_0 == 99u32 && _call_0 == 99u32)]
#[ensures(result == 99u32)]
pub fn g(x: u32) -> u32 { id(x) }
