//@ expect: reject
//@ mechanism: a `&mut` parameter's POINTEE written by a plain store of a value its precondition says
//@ mechanism: nothing about, then a `proof_assert!` of the pointee's ENTRY value: `*x = any();
//@ mechanism: proof_assert!((*x)@ == 0)` under `#[requires((*x)@ == 0)]`, the same through a reborrow
//@ mechanism: (`let r = &mut *x; *r = any();`), and a store of another parameter (`*x = y`). The
//@ mechanism: proof_assert lane binds the pointee to the value written (a store of 7 is proved `== 7`,
//@ mechanism: and a store of 7 under `(*x)@ == 0` is refused as a vacuous proof) and reads the
//@ mechanism: precondition, a fact about the entry pointee under the same name, beside that binding, so
//@ mechanism: the entry fact constrains the call's result or `y`. D-140's withdrawal of re-bound
//@ mechanism: parameters' entry facts asks a hand-off of every parameter and a plain write only of a
//@ mechanism: BY-VALUE parameter; a `&mut` parameter's pointee written by a plain store is withdrawn by
//@ mechanism: nothing. Found probing that withdrawal sideways; no drop and no loop is involved.
//@ accept-means: a `proof_assert!` is credited from a `&mut` parameter's entry precondition after the body
//@ accept-means: overwrote the pointee with a value the precondition says nothing about, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: at each assertion the pointee holds 9 (what `any` returns) or `y`;
//@ WHY THE CONTRACT IS FALSE: `store_param_value(&mut 0, 5)` asserts `5 == 0`.
//@ fixed-by: D-185 (the entry pointee and the stored value are named apart: the store's binding is no
//@ fixed-by: fact about `x_current`, and the assertion reads `*x` as the stored value, or is refused as a
//@ fixed-by: stale read after the store through the reborrow)
//@ teeth: LIVE: each function ACCEPTED, exit 0, `proof_assert in creusot_test::<fn> verified`, on D-140's
//@ teeth: driver and on the campaign driver it branches from.
//@ also-verified: any
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(true)]
#[ensures(true)]
pub fn any() -> u32 {
    9
}

#[requires((*x)@ == 0)]
pub fn store_through_param(x: &mut u32) {
    *x = any();
    proof_assert!((*x)@ == 0);
}

#[requires((*x)@ == 0)]
pub fn store_through_reborrow(x: &mut u32) {
    let r = &mut *x;
    *r = any();
    proof_assert!((*x)@ == 0);
}

#[requires((*x)@ == 0)]
pub fn store_param_value(x: &mut u32, y: u32) {
    *x = y;
    proof_assert!((*x)@ == 0);
}
