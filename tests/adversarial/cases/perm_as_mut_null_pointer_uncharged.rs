//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: the `Perm::as_mut` sibling of perm_as_ref_null_pointer_uncharged.rs. The builtin spec
//@ mechanism: states no precondition; Creusot's requires `ptr as *const T == *own.ward()`.
//@ accept-means: a std spec that omits its safety precondition lets a body that writes through a null
//@ accept-means: pointer on every call verify.
//@ accept-means: `f()` aborts on every call: `Perm::as_mut` is `&mut *ptr` on a null pointer.
//@ fixed-by: D-138 — the call owes `ptr == *own.ward()`, and takes its permission uniquely.
//@ teeth: ACCEPTED (`f verified`, exit 0) when committed; FAILED on the owed ward under D-138.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

#[ensures(true)]
pub fn f() {
    let (_p, mut own) = Perm::new(1i32);
    let r = unsafe { Perm::as_mut(std::ptr::null_mut::<i32>(), ghost!(&mut *own)) };
    *r = 3;
}
