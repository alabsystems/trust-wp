//@ expect: reject
//@ verdict: failed
//@ fn-failed: f
//@ mechanism: the builtin spec of `Perm::to_box(ptr, own)` states no precondition, and the ghost
//@ mechanism: validator's permission-identity check covers `as_ref`/`as_mut` only. Creusot's contract
//@ mechanism: requires `ptr as *const T == *own.ward()`, so each allocation is boxed back by the one
//@ mechanism: permission that owns it, once. Here `p` is boxed twice, once under `q`'s permission.
//@ accept-means: a std spec that omits its safety precondition lets a body that frees one allocation
//@ accept-means: twice on every call verify.
//@ accept-means: `f()` aborts on every call: both boxes own `p`, and the second drop frees it again
//@ accept-means: (the allocator traps; exit 133 on aarch64-apple-darwin).
//@ fixed-by: D-138 — `to_box` owes `ptr == *own.ward()`: `own_q` guards `_q`, not `p`.
//@ teeth: ACCEPTED (`f verified`, exit 0) when committed; FAILED on the owed ward under D-138.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

#[ensures(true)]
pub fn f() {
    let (p, own) = Perm::new(1i32);
    let (_q, own_q) = Perm::new(2i32);
    let _b1 = unsafe { Perm::to_box(p, own_q) };
    let _b2 = unsafe { Perm::to_box(p, own) };
}
