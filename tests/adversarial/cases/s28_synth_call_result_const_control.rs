//@ expect: verify
//@ mechanism: consts spelled like the OLD call-result names are ordinary values now; they must not be refused or confused with call results.
//@ fixed-by: wp-s28 (synthesized_names `$` namespace)
//@ teeth: control for s28_synth_const_call_result.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(non_upper_case_globals)]
pub const call_0: u32 = 99;
#[allow(non_upper_case_globals)]
pub const _call_0: u32 = 99;

#[ensures(result == v)]
pub fn id(v: u32) -> u32 { v }

#[requires(call_0 == 99u32 && _call_0 == 99u32)]
#[ensures(result == x)]
pub fn g(x: u32) -> u32 { id(x) }
