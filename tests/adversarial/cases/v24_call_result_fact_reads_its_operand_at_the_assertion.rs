//@ expect: reject
//@ mechanism: the snapshot's `Rc`/`Arc` call facts (`clone`: result == receiver; `ptr_eq`: result
//@ mechanism: and the operands' equality) were built for every such call in the body, with the
//@ mechanism: operands read by name at the assertion: `let r2 = r.clone(); r = Rc::new(2);` made
//@ mechanism: `r2 == r` a fact about the new `r` (rcr), and a `ptr_eq` taken before `r` was
//@ mechanism: re-bound to a clone of `r2` read the new `r` (rcp). The facts are now stated only where
//@ mechanism: the call's return point dominates the assertion and neither the destination nor an
//@ mechanism: operand (nor the place it borrows) is written on a path between (FactScope, D-190).
//@ accept-means: a fact about a call's operands is read of values they took after the call.
//@ WHY THE CONTRACT IS FALSE: rcr: r holds 2 and r2 holds 1. rcp: r and r2 are two allocations
//@ WHY THE CONTRACT IS FALSE: when ptr_eq runs, so b is false.
//@ fixed-by: D-190
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on a3819cee the assertions of rcr and rcp VERIFIED; with D-190 both FAILED.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use ::std::rc::Rc;
use creusot_std::prelude::*;

pub fn rcr() {
    let mut r = Rc::new(1i32);
    let r2 = r.clone();
    r = Rc::new(2i32);
    proof_assert!(r == r2);
}

pub fn rcp() {
    let mut r = Rc::new(1i32);
    let r2 = Rc::new(1i32);
    let b = Rc::ptr_eq(&r, &r2);
    r = r2.clone();
    proof_assert!(b);
}
