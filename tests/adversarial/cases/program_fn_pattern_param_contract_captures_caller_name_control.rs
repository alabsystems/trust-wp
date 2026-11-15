//@ expect: verify
//@ mechanism: control for program_fn_pattern_param_contract_captures_caller_name: the caller claims 7.
//@ fixed-by: D-177 (the pattern binding is its parameter's projection, not a free name a caller captures).
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == a)]
pub fn g((a, _b): (u32, u32)) -> u32 { a }

#[ensures(result == 7u32)]
pub fn h(a: u32) -> u32 { g((7, a)) }
