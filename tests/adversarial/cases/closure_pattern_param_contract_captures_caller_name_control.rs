//@ expect: verify
//@ mechanism: control for closure_pattern_param_contract_captures_caller_name: the argument's first
//@ mechanism: component is 1.
//@ fixed-by: D-177 (the pattern binding is its parameter's projection, not a free name a caller captures).
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(p@ == 1)]
#[ensures(result@ == 1)]
pub fn h(p: u32) -> u32 {
    let f = #[ensures(result == p)] |(p, _q): (u32, u32)| p;
    f((1, 7))
}
