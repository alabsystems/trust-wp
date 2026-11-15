//@ expect: reject
//@ mechanism: the trait-default spelling of param_pattern_projection_read_as_module_const. The
//@ mechanism: default body destructures its second parameter, D-177 rewrites the trait's clause
//@ mechanism: `result == a` to `result == (arg1.0)`, and the module's const `arg1` is inlined into
//@ mechanism: that text when the default body is verified against it.
//@ accept-means: a trait default's pattern binding was read as a module constant spelled like the
//@ accept-means: parameter's positional name.
//@ WHY THE CONTRACT IS FALSE: `W.m((7, 0))` runs the default body and returns 5, not 7.
//@ fixed-by: D-179, with param_pattern_projection_read_as_module_const: the trait's clause is
//@ fixed-by: `result == (__twp_arg1.0)`.
//@ teeth: ACCEPTED (exit 0, `Tr::m verified`) at the reviewed head and with every crate checked out at
//@ teeth: the campaign base in place.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(non_upper_case_globals)]
pub const arg1: (u32, u32) = (5, 5);

pub trait Tr {
    #[ensures(result == a)]
    fn m(&self, (a, _b): (u32, u32)) -> u32 {
        5u32
    }
}

pub struct W;

impl Tr for W {}
