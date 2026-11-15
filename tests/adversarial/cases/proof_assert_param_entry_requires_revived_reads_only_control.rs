//@ expect: verify
//@ xfail: the reassigned struct (`p = P { x: 7 }`) is FAILED: its assertion `p.x@ == 7` is not proved
//@ xfail: from the constructor the substitution binds `p` to. The scalar, `&mut` pointee and `consume`
//@ xfail: spellings verify: D-140 withdraws the entry precondition of a by-value parameter the body
//@ xfail: re-binds, which the lane had read as a fact about its current binding (a vacuous proof after
//@ xfail: `x = 7`). No hand-off is involved: the `Drop` here only reads.
//@ mechanism: control for proof_assert_param_entry_requires_revived_by_drop_glue: the same four functions
//@ mechanism: over a guard whose `Drop` impl only reads through the borrow, each asserting the value the
//@ mechanism: body wrote (7), which is true.
//@ accept-means: n/a (control)
//@ teeth: n/a — over-refusal control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        let _ = *self.0;
    }
}

pub struct P {
    pub x: u32,
}

#[requires(x@ == 0)]
pub fn scalar_param(mut x: u32) {
    x = 7;
    {
        let _g = G(&mut x);
    }
    proof_assert!(x@ == 7);
}

#[requires((*x)@ == 0)]
pub fn mut_pointee(x: &mut u32) {
    *x = 7;
    {
        let _g = G(&mut *x);
    }
    proof_assert!((*x)@ == 7);
}

#[requires(p.x@ == 0)]
pub fn struct_param(mut p: P) {
    p = P { x: 7 };
    {
        let _g = G(&mut p.x);
    }
    proof_assert!(p.x@ == 7);
}

#[requires(true)]
pub fn consume(_g: G<'_>) {}

#[requires(x@ == 0)]
pub fn verified_consume(mut x: u32) {
    x = 7;
    consume(G(&mut x));
    proof_assert!(x@ == 7);
}
