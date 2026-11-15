//@ expect: verify
//@ mechanism: control for return_field_borrow_write_lost — the same program with the postcondition the write actually establishes.
//@ accept-means: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub struct S {
    pub a: i32,
    pub b: i32,
}

#[ensures(result.a == 7i32)]
pub fn k() -> S {
    let mut s = S { a: 5, b: 6 };
    let r = &mut s.a;
    *r = 7;
    s
}
