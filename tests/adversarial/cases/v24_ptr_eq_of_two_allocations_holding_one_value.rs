//@ expect: reject
//@ mechanism: `Rc::ptr_eq` / `Arc::ptr_eq` were specified as `result == (*self == *rhs)`, but the
//@ mechanism: encoding reads an `Rc` as the value it points to and has no allocation identity, so
//@ mechanism: two allocations holding the same value were `ptr_eq` (the spec's own comment said
//@ mechanism: so). Only the direction the encoding can see is stated now: the same allocation
//@ mechanism: holds the same value (D-190).
//@ accept-means: `ptr_eq` of two distinct allocations is proved true.
//@ WHY THE CONTRACT IS FALSE: two `new` calls make two allocations, so b is false.
//@ fixed-by: D-190
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on a3819cee the assertions of rcn and arn VERIFIED; with D-190 both FAILED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use ::std::{rc::Rc, sync::Arc};
use creusot_std::prelude::*;

pub fn rcn() {
    let r = Rc::new(1i32);
    let r2 = Rc::new(1i32);
    let b = Rc::ptr_eq(&r, &r2);
    proof_assert!(b);
}

pub fn arn() {
    let r = Arc::new(1i32);
    let r2 = Arc::new(1i32);
    let b = Arc::ptr_eq(&r, &r2);
    proof_assert!(b);
}
