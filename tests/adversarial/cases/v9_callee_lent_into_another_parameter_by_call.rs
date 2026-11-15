//@ expect: reject
//@ mechanism: `v.push(p)` moves the borrow of `p` into the vector `v` points to. The
//@ mechanism: mut-borrow lane advanced the call's receiver by the std spec's `^self` equation and
//@ mechanism: left every other `&mut` argument as it was, so `p`'s final value was its entry
//@ mechanism: value and the function proved `^p == *p` of a borrow its caller writes through
//@ mechanism: `v` afterwards. `Option::insert` is the same shape.
//@ accept-means: a function proves the final value of a `&mut` parameter it passed to a call
//@ accept-means: whose spec says nothing of it.
//@ WHY THE CONTRACT IS FALSE: the holder of `v` (or `slot`) may write through the stored borrow
//@ WHY THE CONTRACT IS FALSE: after the call, so `^p` is not `*p`.
//@ fixed-by: D-107 (a spec-advanced call havocs every other `&mut` argument's parameter; the
//@ fixed-by: signature lends `p` into `v`, so `^p` has no reading)
//@ teeth: MEASURED (debug driver) on 576532d7: `stash_push verified`, `stash_insert verified`.
//@ teeth: On the D-107 tree both clauses are refused by name; with the refusal ablated the
//@ teeth: havoc alone leaves `stash_push` FAILED and `stash_insert` unknown.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^p == *p)]
pub fn stash_push<'a>(p: &'a mut i32, v: &mut Vec<&'a mut i32>) {
    v.push(p);
}

#[ensures(^p == *p)]
pub fn stash_insert<'a>(p: &'a mut i32, slot: &mut Option<&'a mut i32>) {
    let _ = slot.insert(p);
}
