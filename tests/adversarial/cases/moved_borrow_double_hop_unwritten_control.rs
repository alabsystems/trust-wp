//@ expect: verify
//@ mechanism: The control for the moved_borrow_double_hop family: the same move and the same
//@ mechanism: `&mut &mut` hop, with NO write through it. `^r == *r` is TRUE here, so this
//@ mechanism: case separates attributing the lost write from refusing the shape wholesale.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32) {
    let mut q = r;
    let s = &mut q;
    let _read = **s;
}
