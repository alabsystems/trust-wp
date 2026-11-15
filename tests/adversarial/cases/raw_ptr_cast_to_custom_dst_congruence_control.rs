//@ expect: verify
//@ mechanism: control for raw_ptr_cast_to_custom_dst_shadowed_binding_not_one_symbol: one pair's
//@ mechanism: function of one pointer is one value (congruence), which the identity also said.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct D {
    pub n: u8,
    pub tail: [u8],
}

#[ensures(result)]
pub fn f(p: *const [u8]) -> bool {
    let a = p as *const D;
    let b = p as *const D;
    a == b
}
