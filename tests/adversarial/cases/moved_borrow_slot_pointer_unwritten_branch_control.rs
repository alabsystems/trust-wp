//@ expect: verify
//@ mechanism: Control for moved_borrow_slot_pointer_branch_write_lost: the same branch and
//@ mechanism: the same slot pointer with a READ instead of a write. `^r == *r` is TRUE, so a
//@ mechanism: fix that havocs on the mere existence of the pointer would break this.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^r == *r)]
pub fn f(r: &mut i32, c: bool) {
    let mut q = r;
    let s = &mut q;
    if c {
        let _read = **s;
    }
}
