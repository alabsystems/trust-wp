//@ expect: verify
//@ mechanism: control for struct_held_borrow_write_lost — the same program asserting the value the write actually leaves behind.
//@ accept-means: n/a (control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
pub struct H<'a> {
    pub p: &'a mut i32,
}

pub fn k() {
    let mut x = 5i32;
    let h = H { p: &mut x };
    *h.p = 7;
    proof_assert!(x == 7i32);
}
