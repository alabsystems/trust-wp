//@ expect: verify
//@ mechanism: control for program_fn_pattern_param_requires_captures_caller_name: the caller passes
//@ mechanism: its own positive `a` as the first component.
//@ fixed-by: D-177 (the pattern binding is its parameter's projection, not a free name a caller captures).
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(a > 0u32)]
pub fn g((a, _b): (u32, u32)) -> u32 { 100 / a }

#[requires(a > 0u32)]
pub fn h(a: u32) -> u32 { g((a, 0)) }
