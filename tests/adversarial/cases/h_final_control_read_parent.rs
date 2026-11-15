//@ expect: verify
//@ mechanism: control for the h_final_* family — a FINAL reborrow whose whole-borrow equality Creusot proves; a fix that makes every reborrow fresh breaks this
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn read_parent_after_reborrow(bor: &mut i32) {
    let b1 = &mut *bor;
    let _v = *bor; // a copy-read of the parent is not a move/borrow/write: b1 stays final
    proof_assert!(b1 == bor);
}
