//@ expect: reject
//@ mechanism: a pre-Creusot clause's bare `*p` is the value `p` is left with. `leak` lends `p`
//@ mechanism: into the `*mut i32` it returns, so that value is its caller's to decide, and the
//@ mechanism: callee's lane read the `*p` at ENTRY instead (the lent exception of the `*p -> ^p`
//@ mechanism: rewrite): `*p == old(*p)` became `entry == entry`. The call decided lending from the
//@ mechanism: regions of the return type alone, saw none in `*mut i32`, and read the same `*p` as
//@ mechanism: `^p`: the caller was credited with `^x == *x`, a reading no lane proved.
//@ accept-means: a callee proves a pre-Creusot clause of a lent parameter at entry, or a caller is
//@ accept-means: credited with a reading of a callee clause its lane did not prove.
//@ WHY THE CONTRACT IS FALSE: `leak` stores 5 through the borrow of `x`, so `^x` is 5 and the
//@ WHY THE CONTRACT IS FALSE: precondition makes the entry `*x` something else; `leak`'s own
//@ WHY THE CONTRACT IS FALSE: `*p == old(*p)` is false of the same store.
//@ fixed-by: D-102 (whether the result may borrow a `&mut` parameter is a fact of the signature,
//@ fixed-by: `mut_borrow::may_carry_borrow` of the return type; a pre-Creusot read of a lent final
//@ fixed-by: value is refused in the function's lane and at every call alike)
//@ teeth: MEASURED on cbadb52d (debug driver): `leak verified`, `leak_caller verified`. d454c1e1:
//@ teeth: `leak verified`, caller unknown. On the D-102 tree: leak refused, caller unknown.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(*p == old(*p))]
pub fn leak(p: &mut i32) -> *mut i32 {
    *p = 5;
    p as *mut i32
}

#[requires(*x != 5i32)]
#[ensures(^x == *x)]
pub fn leak_caller(x: &mut i32) {
    let _ = leak(x);
}
