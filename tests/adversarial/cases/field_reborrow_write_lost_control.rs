//@ expect: verify
//@ xfail: the post-state of field_reborrow_write_lost is not provable today — the write through the field borrow reaches nothing, so neither twin can be discharged. OBSERVED verdict: failed. Retire this xfail when a borrow chain follows the projection in the borrowed place.
//@ mechanism: control for field_reborrow_write_lost — the same program asserting the value the write actually leaves behind, and that the sibling field is untouched.
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

pub fn k() {
    let mut s = S { a: 5, b: 6 };
    let r = &mut s.a;
    *r = 7;
    proof_assert!(s.a == 7i32 && s.b == 6i32);
}
