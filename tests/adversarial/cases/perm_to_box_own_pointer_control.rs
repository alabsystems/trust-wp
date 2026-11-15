//@ expect: verify
//@ mechanism: the TRUE twin of perm_to_box_other_pointer_double_free_uncharged.rs: each pointer is
//@ mechanism: boxed back once, by the permission `Perm::new` returned with it.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified`, exit 0, when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

#[ensures(true)]
pub fn f() {
    let (p, own) = Perm::new(1i32);
    let (q, own_q) = Perm::new(2i32);
    let _b1 = unsafe { Perm::to_box(q, own_q) };
    let _b2 = unsafe { Perm::to_box(p, own) };
}
