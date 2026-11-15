//@ expect: verify
//@ xfail: D-129: a proof_assert reads no local a holder of its borrow may have written, and D-127
//@ xfail: counts a drop of a value holding a borrow, or a call handed one, as a write through it
//@ xfail: whatever the `Drop` impl's body does, so every assertion here is refused as a stale read.
//@ mechanism: control for proof_assert_entry_requires_pins_param_after_drop_glue: the same functions
//@ mechanism: over a guard whose `Drop` impl only reads through the borrow, so each parameter keeps its
//@ mechanism: entry value and each assertion is true.
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
pub fn scalar_scope_end(mut x: u32) {
    {
        let _g = G(&mut x);
    }
    proof_assert!(x@ == 0);
}

#[requires(x@ == 0)]
pub fn scalar_mem_drop(mut x: u32) {
    let g = G(&mut x);
    std::mem::drop(g);
    proof_assert!(x@ == 0);
}

#[requires(p.x@ == 0)]
pub fn struct_field(mut p: P) {
    {
        let _g = G(&mut p.x);
    }
    proof_assert!(p.x@ == 0);
}

#[requires((*x)@ == 0)]
pub fn mut_pointee(x: &mut u32) {
    {
        let _g = G(&mut *x);
    }
    proof_assert!((*x)@ == 0);
}

#[requires(true)]
pub fn consume(_g: G<'_>) {}

#[requires(x@ == 0)]
pub fn verified_consume(mut x: u32) {
    consume(G(&mut x));
    proof_assert!(x@ == 0);
}

#[requires(x@ == 0)]
pub fn after_loop(mut x: u32) {
    let mut i = 0u32;
    #[invariant(i@ <= 3)]
    while i < 3 {
        i += 1;
    }
    {
        let _g = G(&mut x);
    }
    proof_assert!(x@ == 0);
}
