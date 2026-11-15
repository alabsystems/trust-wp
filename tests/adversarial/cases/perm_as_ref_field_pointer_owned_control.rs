//@ expect: verify
//@ mechanism: the TRUE twin of perm_as_ref_field_pointer_unrelated_uncharged.rs, bug/1743.rs's shape:
//@ mechanism: the caller requires the permission to guard the pointer it dereferences.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified`, exit 0, when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

pub struct S {
    pub ptr: *const i32,
    pub perm: Ghost<Box<Perm<*const i32>>>,
}

#[requires(*s.perm.ward() == s.ptr)]
#[ensures(true)]
pub fn f(s: S) -> i32 {
    let r = unsafe { Perm::as_ref(s.ptr, ghost!(&*s.perm)) };
    *r
}
