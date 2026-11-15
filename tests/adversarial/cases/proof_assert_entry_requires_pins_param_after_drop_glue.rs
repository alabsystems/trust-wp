//@ expect: reject
//@ mechanism: drop glue that writes a PARAMETER, then a `proof_assert!` about it: a by-value scalar
//@ mechanism: parameter borrowed into a guard (`{ let _g = G(&mut x); }`, `mem::drop(g)`, a verified
//@ mechanism: `consume(G(&mut x))`, and the scope end after a loop), a field of a by-value struct parameter
//@ mechanism: (`G(&mut p.x)`), and a `&mut` parameter's pointee reborrowed into one (`G(&mut *x)`), where
//@ mechanism: `G::drop` stores 5 through the borrow. D-140's substitution walk
//@ mechanism: re-binds the parameter to a fresh symbol at the hand-off, but the proof_assert lane reads a
//@ mechanism: `#[requires]` fact about a parameter as a fact about the parameter's CURRENT binding (the
//@ mechanism: encoder gives the entry and the current value one symbol). A direct write collides with that
//@ mechanism: fact and is refused as a vacuous proof; the hand-off's fresh value collides with nothing, so
//@ mechanism: the entry precondition `x@ == 0` becomes a premise about the value the glue wrote, and the
//@ mechanism: assertion is proved. The same write reached by a call
//@ mechanism: (`set5(&mut x)` with `ensures((^x)@ == 5)`, or `touch(&mut x)` with `ensures(true)`) is
//@ mechanism: refuted, and so is the glue writing a LOCAL copied from the parameter (`let mut c = x;
//@ mechanism: G(&mut c)`, drop_glue_write_seen_by_proof_assert_unseen's shape).
//@ accept-means: a `proof_assert!` about a parameter is credited from its entry precondition after drop glue
//@ accept-means: overwrote it, and the crate exits 0.
//@ WHY THE CONTRACT IS FALSE: at each assertion the asserted value is 5: the guard is dropped before it and
//@ WHY THE CONTRACT IS FALSE: `G::drop` stores 5 through the borrow of the parameter (or of its field, or of
//@ WHY THE CONTRACT IS FALSE: its pointee); the precondition says only that it was 0 at entry.
//@ fixed-by: D-140: the proof_assert lane withdraws the entry facts, and the loop-exit facts it reads
//@ fixed-by: through the assertion's substitution, that name a parameter a hand-off before the assertion
//@ fixed-by: may re-bind (`after_loop` came back as a loop-exit fact the loop lane carried across the loop).
//@ teeth: MEASURED on one binary with the withdrawal disabled by an env knob (never committed): ACCEPTED,
//@ teeth: exit 0, each `proof_assert in creusot_test::<fn> verified` and each function `verified`; with the
//@ teeth: hand-off withdrawal alone, each assertion and function is FAILED. Control:
//@ teeth: proof_assert_entry_requires_param_drop_glue_reads_only_control (the same functions over a `Drop`
//@ teeth: that only reads), verified either way. The same assertion inside a loop after the glue is FAILED
//@ teeth: too, its function `unknown` on a fail-closed `false`.
//@ also-verified: <G<'_> as std::ops::Drop>::drop, consume
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct G<'a>(pub &'a mut u32);

impl Drop for G<'_> {
    #[requires(true)]
    fn drop(&mut self) {
        *self.0 = 5;
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
