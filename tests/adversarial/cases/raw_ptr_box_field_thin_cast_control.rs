//@ expect: verify
//@ mechanism: control for raw_ptr_box_field_fat_to_thin_cast_read_as_operand: a boxed field's thin
//@ mechanism: cast is a function of the field (congruence).
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S {
    pub p: *const [u8],
}

#[ensures(result)]
pub fn f(s: Box<S>) -> bool {
    let a = s.p as *const u8;
    let b = s.p as *const u8;
    a == b
}
