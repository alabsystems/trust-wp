//@ expect: reject
//@ verdict: error
//@ refused-with: `x_current` is spelled as a name the verifier derives from `x`
//@ mechanism: parameters of a bodiless trait method were not in the derived-name value set; `x_current` next to `x: &mut u32` is the solver variable for `*x`.
//@ fixed-by: wp-s28 v8 (validate_derived_name_aliases takes fn_arg_idents of bodiless functions)
//@ accept-means: the trait contract `result == x_current` was read as `result == *x`.
//@ teeth: exit 2 with the derived-name refusal on v8 (the impl names the parameter `y`, so only the bodiless declaration spells `x_current`); not measured before the fix.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait T {
    #[ensures(result == x_current)]
    fn m(x: &mut u32, x_current: u32) -> u32;
}

pub struct S;

impl T for S {
    fn m(x: &mut u32, y: u32) -> u32 { let _ = y; *x }
}
