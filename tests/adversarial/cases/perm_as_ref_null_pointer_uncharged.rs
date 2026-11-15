//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: the builtin spec of `Perm::as_ref(ptr, own)` states no precondition, so the call owes
//@ mechanism: nothing about `ptr`. Creusot's contract requires `ptr == *own.ward()`: the pointer is the
//@ mechanism: one the permission guards. The permission-identity check in the ghost validator reads
//@ mechanism: only a resource bound to a local; a pointer written inline reaches no check at all.
//@ accept-means: a std spec that omits its safety precondition lets a body that dereferences a null
//@ accept-means: pointer on every call verify.
//@ accept-means: `f()` aborts on every call: `Perm::as_ref` is `&*ptr` on a null pointer ("null
//@ accept-means: reference produced" under debug assertions; a null dereference without them).
//@ fixed-by: D-138 — the call owes Creusot's `ptr == *own.ward()`; `Perm::new` states the ward it returns.
//@ teeth: ACCEPTED (`f verified`, exit 0) when committed; FAILED on the owed ward under D-138.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

#[ensures(true)]
pub fn f() -> i32 {
    let (_p, own) = Perm::new(1i32);
    let r = unsafe { Perm::as_ref(std::ptr::null::<i32>(), ghost!(&*own)) };
    *r
}
