//@ expect: verify
//@ mechanism: control for logic_free_fn_pattern_param_captures_caller_name: the body returns `a`.
//@ fixed-by: D-177 (the pattern binding is its parameter's projection, not a free name a caller captures).
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[logic(open)]
pub fn k((p, _q): (Int, Int)) -> Int { p }

#[ensures(result@ == k((a@, b@)))]
pub fn g(p: u32, a: u32, b: u32) -> u32 { a }
