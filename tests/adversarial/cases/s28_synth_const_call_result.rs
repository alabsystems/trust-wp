//@ expect: reject
//@ mechanism: call results were Var("call_N") / Var("_call_N"); consts of those names were the same solver symbols, so a true requires over the consts
//@ mechanism: pinned the call result. Call results are now `$call_N` / `$_call_N`, which no identifier can spell.
//@ fixed-by: wp-s28 (synthesized_names `$` namespace)
//@ accept-means: g proved result == 99 for an arbitrary x.
//@ teeth: exit-0 false accept at 3eede3c2 and c030a10d (review rv7/d3); renamed consts (d3n) FAILED.
//@ also-verified: id
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(non_upper_case_globals)]
pub const call_0: u32 = 99;
#[allow(non_upper_case_globals)]
pub const call_1: u32 = 99;
#[allow(non_upper_case_globals)]
pub const call_2: u32 = 99;
#[allow(non_upper_case_globals)]
pub const call_3: u32 = 99;
#[allow(non_upper_case_globals)]
pub const _call_0: u32 = 99;
#[allow(non_upper_case_globals)]
pub const _call_1: u32 = 99;
#[allow(non_upper_case_globals)]
pub const _call_2: u32 = 99;
#[allow(non_upper_case_globals)]
pub const _call_3: u32 = 99;

#[ensures(result == v)]
pub fn id(v: u32) -> u32 { v }

// WRONG: returns x, which is arbitrary.
#[requires(call_0 == 99u32 && call_1 == 99u32 && call_2 == 99u32 && call_3 == 99u32 && _call_0 == 99u32 && _call_1 == 99u32 && _call_2 == 99u32 && _call_3 == 99u32)]
#[ensures(result == 99u32)]
pub fn g(x: u32) -> u32 { id(x) }
