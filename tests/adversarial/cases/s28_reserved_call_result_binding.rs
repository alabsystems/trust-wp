//@ expect: reject
//@ mechanism: the call-result symbol `call_{N}` (extract::call_args::call_result_symbol) was the SAME solver
//@ mechanism: symbol as a source parameter literally named `call_{N}`; call results are now `$call_{N}`, so the
//@ mechanism: parameter is an ordinary unrelated value and the false contract FAILS.
//@ fixed-by: wp-s28 (trust_wp_core::formula::synthesized_names)
//@ accept-means: g proved its result equals an arbitrary parameter because the parameter aliased id(7)'s result.
//@ teeth: exit-0 false accept on 9303bb3b (probes6/p_cn1); the same file with renamed parameters FAILED (p_cn1n).
//@ also-verified: id
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == v)]
pub fn id(v: u32) -> u32 { v }

// WRONG: g returns 7 whatever its arguments are.
#[ensures(result == call_0 || result == call_1 || result == call_2 || result == call_3)]
pub fn g(call_0: u32, call_1: u32, call_2: u32, call_3: u32) -> u32 { id(7) }
