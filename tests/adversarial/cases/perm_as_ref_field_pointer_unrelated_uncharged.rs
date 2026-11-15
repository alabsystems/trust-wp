//@ expect: reject
//@ mechanism: bug/1743.rs without its `requires(*self.perm.ward() == self.ptr)`. The pointer and the
//@ mechanism: permission are fields of a parameter, which the ghost validator's same-origin check
//@ mechanism: cannot read, and the builtin spec of `Perm::as_ref` owes nothing, so a pointer no
//@ mechanism: permission guards is dereferenced unchecked.
//@ accept-means: a std spec that omits its safety precondition lets a body verify whose contract
//@ accept-means: admits an input it dereferences as a null pointer.
//@ accept-means: `f(S { ptr: std::ptr::null(), perm })` aborts, for `perm` any permission, for
//@ accept-means: example the one `Perm::new(1i32)` returns.
//@ fixed-by: D-138 — the call owes `ptr == *own.ward()`, which nothing in `f` states.
//@ teeth: ACCEPTED (`f verified`, exit 0) when committed; `unknown (incomplete)` under D-138, whose
//@ teeth: owed ward has no counterexample the model validator confirms.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

pub struct S {
    pub ptr: *const i32,
    pub perm: Ghost<Box<Perm<*const i32>>>,
}

#[ensures(true)]
pub fn f(s: S) -> i32 {
    let r = unsafe { Perm::as_ref(s.ptr, ghost!(&*s.perm)) };
    *r
}
