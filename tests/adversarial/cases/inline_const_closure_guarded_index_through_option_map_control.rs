//@ expect: verify
//@ mechanism: control for inline_const_closure_index_through_option_map_uncharged: the same inline
//@ mechanism: `const { }` closure handed to `Option::map`, its index guarded by the array's length.
//@ mechanism: A fix that makes the closure a target must keep this verifying.
//@ accept-means: n/a (control)
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == k@)]
pub fn pick(o: Option<usize>, k: u32) -> u32 {
    let _ = o.map(const { |j: usize| if j < 2 { [1u32, 2][j] } else { 0 } });
    k
}
